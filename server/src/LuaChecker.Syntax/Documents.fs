namespace rec LuaChecker.Syntax
open LuaChecker
open LuaChecker.Primitives


type Source<'T> = Token<'T, Span>
[<Struct>]
type Name<'Document> = Name of Token<string, Trivia<'Document>>

type FieldSepKind =
    | Comma
    | Semicolon

module Documents =
    open LuaChecker.Syntax


    type ParseResult = (struct(Document list * ParseError list))

    type Trivia = Trivia<HEmpty>
    type Token<'T> = Token<'T, Trivia>
    type Token = Token<HEmpty, Trivia>
    type Name = HEmpty Name

    [<Struct>]
    type Comment = Comment of Source<string>

    type Parameter = Parameter' Source
    /// (name ":")? typeSign
    type Parameter' = Parameter of nameAndColon: (Name * Token) option * TypeSign

    type VariadicTypeSign = VariadicTypeSign' Source
    /// name? "..." constrainedType?
    type VariadicTypeSign' = VariadicTypeSign of typeParameterName: Name option * dot3: Token * allElementTypeConstraint: TypeSign option

    type Field = Field' Source
    type Field' = Field of FieldKey Source * colon: Token * TypeSign

    type Fields = Fields' Source
    /// "{" field (fieldSep field)* fieldSep? "}"
    type Fields' = Fields of lcBracket: Token * fields: SepBy<Token<FieldSepKind>, Field> * lastFieldSep: Token<FieldSepKind> option * rcBracket: Token
    type TypeConstraints = Fields

    /// parameter ("," parameter)*
    type Parameters = Parameters of SepBy<Token, Parameter>

    /// "<" typeSign ("," typeSign)* ","? ">"
    type GenericArguments = GenericArguments of lt: Token * SepBy<Token, TypeSign> * lastComma: Token option * gt: Token

    type TypeSign = TypeSign' Source
    type TypeSign' =
        /// "(" ")"
        | EmptyType of lBracket: Token * rBracket: Token

        ///<summary>`function` `table&lt;number, string&gt;`</summary>
        | NamedType of name: Name * GenericArguments option

        /// "(" parameter "," ")"
        | SingleMultiType of lBracket: Token * Parameter * comma: Token * rBracket: Token

        /// "(" typeSign ")"
        | WrappedType of lBracket: Token * TypeSign * rBracket: Token

        /// `{ name: string, age: number }`
        | InterfaceType of Fields

        | VariadicType of VariadicTypeSign

        /// typeSign "[" "]"
        | ArrayType of TypeSign * lsBracket: Token * rsBracket: Token

        /// T: { x: number }
        | ConstrainedType of TypeSign * colon: Token * TypeConstraints

        /// `fun()` `fun(x: string, number): ()` `fun(...): ()`
        | FunctionType of funNameToken: Token * lBracket: Token * Parameters option * rBracket: Token * colon: Token * TypeSign

        /// parameter "," parameters
        | MultiType2 of Parameter * comma: Token * Parameters

    [<RequireQualifiedAccess>]
    type Visibility =
        | Public
        | Protected
        | Private

    type TypeParameter = TypeParameter' Source
    type TypeParameter' =
        /// name (":" constraints)?
        | TypeParameter of Name * colonAndConstraints: (Token * TypeConstraints) option
        /// name "..." constrainedType?
        | VariadicTypeParameter of Name * dot3: Token * TypeSign option

    type TagTail = TagTail' Source
    type TagTail' =

        /// (?<= "@" name) comment
        | UnknownTag of tagName: Name * Comment

        /// (?<= "@" "type") type
        | TypeTag of tagName: Token * TypeSign

        /// (?<= "@" "global") name type
        | GlobalTag of tagName: Token * Name * TypeSign

        /// (?<= "@" "_Feature") name
        | FeatureTag of tagName: Token * Name

        /// (?<= "@" "class") name (":" type)
        | ClassTag of tagName: Token * Name * colonAndType: (Token * TypeSign) option

        /// (?<= "@" "field") ("public" | "protected" | "private")? fieldKey type
        | FieldTag of tagName: Token * Visibility Source option * FieldKey Source * TypeSign

        /// (?<= "@" "generic") typeParameter ("," typeParameter)*
        | GenericTag of tagName: Token * SepBy<Token, TypeParameter>

    type Tag = Tag' Source
    /// "@" name tagElement
    type Tag' = Tag of at: Token * TagTail

    type Document = Document' Source
    /// comment tag*
    type Document' = Document of summary: Comment * Tag list
