namespace rec LuaChecker.Syntax
open LuaChecker
open LuaChecker.Primitives


type Source<'T> = Token<'T, Span>
[<Struct>]
type Name<'Document> = Name of Token<string, Trivia<'Document>>


module Documents =
    open LuaChecker.Syntax


    type ParseResult = (struct(Document list * ParseError list))

    type Trivia = Trivia<HEmpty>
    type Token<'T> = Token<'T, Trivia>
    type Token = Token<HEmpty, Trivia>
    type Name = HEmpty voption Name

    [<Struct>]
    type Comment = Comment of Source<string>

    type Parameter = Parameter' Source
    type Parameter' = Parameter of Name option * TypeSign
    type VariadicParameter = VariadicParameter' Source
    [<Struct>]
    type VariadicParameter' = VariadicParameter of name: Name option * allElementTypeConstraint: TypeSign option

    type Field = Field' Source
    type Field' = Field of FieldKey Source * TypeSign

    type Fields = Fields' Source
    type Fields' = Fields of Field NonEmptyList
    type TypeConstraints = Fields

    type TypeSign = TypeSign' Source
    type TypeSign' =
        | MultiType of Parameter list * VariadicParameter option

        ///<summary>`function` `table&lt;number, string&gt;`</summary>
        | NamedType of name: Name * genericArguments: TypeSign list

        /// `string[]`
        | ArrayType of TypeSign

        /// `{ name: string, age: number }`
        | InterfaceType of Fields

        /// T: { x: number }
        | ConstrainedType of TypeSign * TypeConstraints

        /// `fun()` `fun(x: string, number): ()` `fun(...): ()`
        | FunctionType of TypeSign * TypeSign

    [<RequireQualifiedAccess>]
    type Visibility =
        | Public
        | Protected
        | Private

    type TypeParameter = TypeParameter' Source
    type TypeParameter' =
        /// name (":" constraints)?
        | TypeParameter of Name * TypeConstraints option
        /// name "..." constrainedType?
        | VariadicTypeParameter of Name * TypeSign option

    type Tag = Tag' Source
    type Tag' =
        /// "@" name comment
        | UnknownTag of Name * Comment

        /// "@type" type
        | TypeTag of TypeSign

        /// "@global" name type
        | GlobalTag of Name * TypeSign

        /// "@_Feature" name
        | FeatureTag of Name

        /// "@class" name (":" type)
        | ClassTag of Name * TypeSign option

        /// "@field" ("public" | "protected" | "private")? fieldKey type
        | FieldTag of Visibility option * FieldKey Source * TypeSign

        /// "@generic" typeParameter ("," typeParameter)*
        | GenericTag of TypeParameter NonEmptyList

    type Document = Document' Source
    /// comment tag*
    type Document' = Document of summary: Comment * Tag list
