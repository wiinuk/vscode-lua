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


    type ParseResult<'A> = (struct('A Document list * ParseError list))

    type Token<'T> = Token<'T, HEmpty Trivia>
    type Token = HEmpty Source

    [<Struct>]
    type Annotated<'T,'A> = Annotated of target: 'T * annotation: 'A
    type Reserved<'A> = Annotated<Token,'A>
    type Identifier<'A> = Annotated<HEmpty Name,'A>
    type FieldSeparator<'A> = Annotated<FieldSepKind Source,'A>
    type FieldIdentifier<'A> = Annotated<FieldKey Source,'A>
    type FieldVisibility<'A> = Annotated<Visibility Source,'A>

    [<Struct>]
    type Comment = Comment of Source<string>

    type Parameter<'A> = 'A Parameter' Source
    /// (name ":")? typeSign
    type Parameter'<'A> = Parameter of nameAndColon: ('A Identifier * 'A Reserved) option * 'A TypeSign

    type VariadicTypeSign<'A> = 'A VariadicTypeSign' Source
    /// name? "..." constrainedType?
    type VariadicTypeSign'<'A> = VariadicTypeSign of typeParameterName: 'A Identifier option * dot3: 'A Reserved * allElementTypeConstraint: 'A TypeSign option

    type Field<'A> = 'A Field' Source
    type Field'<'A> = Field of 'A FieldIdentifier * colon: 'A Reserved * 'A TypeSign

    type Fields<'A> = 'A Fields' Source
    /// "{" field (fieldSep field)* fieldSep? "}"
    type Fields'<'A> = Fields of lcBracket: 'A Reserved * fields: SepBy<'A FieldSeparator, 'A Field> * lastFieldSep: 'A FieldSeparator option * rcBracket: 'A Reserved
    type TypeConstraints<'A> = 'A Fields

    /// parameter ("," parameter)*
    type Parameters<'A> = Parameters of SepBy<'A Reserved, 'A Parameter>

    /// "<" typeSign ("," typeSign)* ","? ">"
    type GenericArguments<'A> = GenericArguments of lt: 'A Reserved * SepBy<'A Reserved, 'A TypeSign> * lastComma: 'A Reserved option * gt: 'A Reserved

    type TypeSign<'A> = 'A TypeSign' Source
    type TypeSign'<'A> =
        /// "(" ")"
        | EmptyType of lBracket: 'A Reserved * rBracket: 'A Reserved

        ///<summary>`function` `table&lt;number, string&gt;`</summary>
        | NamedType of name: 'A Identifier * 'A GenericArguments option

        /// "(" parameter "," ")"
        | SingleMultiType of lBracket: 'A Reserved * 'A Parameter * comma: 'A Reserved * rBracket: 'A Reserved

        /// "(" typeSign ")"
        | WrappedType of lBracket: 'A Reserved * 'A TypeSign * rBracket: 'A Reserved

        /// `{ name: string, age: number }`
        | InterfaceType of 'A Fields

        | VariadicType of 'A VariadicTypeSign

        /// typeSign "[" "]"
        | ArrayType of 'A TypeSign * lsBracket: 'A Reserved * rsBracket: 'A Reserved

        /// T: { x: number }
        | ConstrainedType of 'A TypeSign * colon: 'A Reserved * 'A TypeConstraints

        /// `fun()` `fun(x: string, number): ()` `fun(...): ()`
        | FunctionType of funNameToken: 'A Reserved * lBracket: 'A Reserved * 'A Parameters option * rBracket: 'A Reserved * colon: 'A Reserved * 'A TypeSign

        /// parameter "," parameters
        | MultiType2 of 'A Parameter * comma: 'A Reserved * 'A Parameters

    [<RequireQualifiedAccess>]
    type Visibility =
        | Public
        | Protected
        | Private

    type TypeParameter<'A> = 'A TypeParameter' Source
    type TypeParameter'<'A> =
        /// name (":" constraints)?
        | TypeParameter of 'A Identifier * colonAndConstraints: ('A Reserved * 'A TypeConstraints) option
        /// name "..." constrainedType?
        | VariadicTypeParameter of 'A Identifier * dot3: 'A Reserved * 'A TypeSign option

    type TagTail<'A> = 'A TagTail' Source
    type TagTail'<'A> =

        /// (?<= "@" name) comment
        | UnknownTag of tagName: 'A Identifier * Comment

        /// (?<= "@" "type") type
        | TypeTag of tagName: 'A Reserved * 'A TypeSign

        /// (?<= "@" "global") name type
        | GlobalTag of tagName: 'A Reserved * 'A Identifier * 'A TypeSign

        /// (?<= "@" "_Feature") name
        | FeatureTag of tagName: 'A Reserved * 'A Identifier

        /// (?<= "@" "class") name (":" type)
        | ClassTag of tagName: 'A Reserved * 'A Identifier * colonAndType: ('A Reserved * 'A TypeSign) option

        /// (?<= "@" "field") ("public" | "protected" | "private")? fieldKey type
        | FieldTag of tagName: 'A Reserved * 'A FieldVisibility option * 'A FieldIdentifier * 'A TypeSign

        /// (?<= "@" "generic") typeParameter ("," typeParameter)*
        | GenericTag of tagName: 'A Reserved * SepBy<'A Reserved, 'A TypeParameter>

    type Tag<'A> = 'A Tag' Source
    /// "@" name tagElement
    type Tag'<'A> = Tag of at: 'A Reserved * 'A TagTail

    type Document<'A> = 'A Document' Source
    /// comment tag*
    type Document'<'A> = Document of summary: Comment * 'A Tag list
