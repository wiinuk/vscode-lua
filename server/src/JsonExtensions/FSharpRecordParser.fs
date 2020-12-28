namespace LuaChecker.Text.Json.Parsing.Internal
open LuaChecker.Text.Json
open System
open System.Diagnostics.CodeAnalysis
open System.Text
open System.Text.Json
open System.Runtime.CompilerServices


type FSharpRecordFieldParser<'F> = {
    utf8Name: byte array
    parser: 'F JsonElementParser
}

module FSharpRecordParser =
    type internal Marker = class end
    [<SuppressMessage("PublicUnusedMemberAnalyzer.fsx", "AA0001:MemberUnused")>]
    [<RequiresExplicitTypeArguments>]
    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let createField<'F> name options = {
        utf8Name = Encoding.UTF8.GetBytes(s = name)
        parser = ParserOptions.getParserOrRaise typeof<'F> options :?> 'F JsonElementParser
    }
    [<SuppressMessage("PublicUnusedMemberAnalyzer.fsx", "AA0001:MemberUnused")>]
    let validateObject (e: JsonElement) = if e.ValueKind <> JsonValueKind.Object then raise <| JsonException()

    [<SuppressMessage("PublicUnusedMemberAnalyzer.fsx", "AA0001:MemberUnused")>]
    let parseField<'F> (e: JsonElement) options f (result: 'F byref) =
        let mutable p = JsonElement()
        if e.TryGetProperty(ReadOnlySpan f.utf8Name, &p) then
            result <- f.parser.Parse(p, options)

namespace LuaChecker.Text.Json.Parsing
open FSharp.Reflection
open LuaChecker.Primitives
open LuaChecker.Quotations
open LuaChecker.Reflection.Emit
open LuaChecker.Text.Json
open LuaChecker.Text.Json.Parsing.Internal
open System
open System.Reflection
open System.Reflection.Emit
open System.Text.Json


module private Emitter =
    type field = class end
    type record = class end
    type parser = record JsonElementParser

    type M = Reflection.MethodAttributes
    type B = Reflection.BindingFlags
    type T = Reflection.TypeAttributes

    type RecordBuilderInfo = {
        recordField: PropertyInfo
        parserField: FieldBuilder
    }

    let defineConstructor (parserT: TypeBuilder) fieldParsers =
        let createFieldMD1 = Expr.findMethodDefinition <@ FSharpRecordParser.createField<_> @>

        //    new (options: ParserOptions) = {
        //        field1 = FSharpRecordParser.createField<'Field1> %Field1.Name options
        //        // ...
        //        fieldN = FSharpRecordParser.createField<'FieldN> %FieldN.Name options
        //    }
        let constructor = parserT.DefineConstructor(M.Public, CallingConventions.Standard, [|typeof<ParserOptions>|])
        constructor.DefineParameter(1, ParameterAttributes.None, "options") |> ignore

        let baseC =
            parserT.BaseType.GetConstructor(B.Instance ||| B.NonPublic ||| B.Public, null, Type.EmptyTypes, null)
            |> ILMethod.declare<args<parser>, result>

        let s = constructor.GetILGenerator() |> ILStack.declare<stack, args<parser, ParserOptions>, result>

        let s = s.Ldarg_0().Call(baseC)
        let s =
            fieldParsers
            |> Array.fold (fun s f ->
                let createFieldM =
                    createFieldMD1.MakeGenericMethod f.recordField.PropertyType
                    |> ILMethod.declare<args<string, ParserOptions>, result<JsonElementParser<field>>>

                let parserF = f.parserField |> ILField.declare<parser, JsonElementParser<field>>

                let s = ILStack.Ldarg_0(s).Ldstr(f.recordField.Name).Ldarg_1().Call(createFieldM).Stfld(parserF)
                s
            ) s

        s.Ret()

    let defineParseMethod (parserT: TypeBuilder) fieldParsers recordConstructor =
        let recordC = ILMethod.declare<args<record>, result> recordConstructor

        // override this.Parse(e: JsonElement, options: ParserOptions): 'RecordType =
        let baseReadM = parserT.BaseType.GetMethod "Parse"
        let readM = parserT.DefineMethod(baseReadM.Name, M.Public ||| M.Virtual ||| M.HideBySig, baseReadM.ReturnType, [| for p in baseReadM.GetParameters() -> p.ParameterType |])
        for p in baseReadM.GetParameters() do
            readM.DefineParameter(p.Position + 1, p.Attributes, p.Name) |> ignore
        let s = ILStack.getILGenerator<args<parser, JsonElement, ParserOptions>, result<record>> readM

        //     let mutable value1: 'Field1 = Unchecked.defaultof<_>
        //     // ...
        //     let mutable valueN: 'FieldN = Unchecked.defaultof<_>
        let locals = [|
            for f in fieldParsers ->
                let local = s.DeclareLocal(the<field>, f.recordField.PropertyType)
                {| local = local; parser = f |}
        |]

        //     FSharpRecordParser.validateObject e
        let validateObjectM =
            Expr.findMethodDefinition <@ FSharpRecordParser.validateObject @>
            |> ILMethod.declare<args<JsonElement>, result>
        let s = s.Ldarg_1().Call(validateObjectM)

        //     FSharpRecordParser.parseField e options this.field1 &value1
        //     // ...
        //     FSharpRecordParser.parseField e options this.fieldN &valueN
        let parseFieldMD1 = typeof<FSharpRecordParser.Marker>.DeclaringType.GetMethod (nameof FSharpRecordParser.parseField)
        let s =
            locals
            |> Array.fold (fun s l ->
                let tryReadFieldM =
                    parseFieldMD1.MakeGenericMethod l.parser.recordField.PropertyType
                    |> ILMethod.declare<args<JsonElement, ParserOptions, FSharpRecordFieldParser<field>, field>, result>

                let parserF =
                    l.parser.parserField
                    |> ILField.declare<parser, FSharpRecordFieldParser<field>>

                let s = ILStack.Ldarg_1(s).Ldarg_2().Ldarg_0().Ldfld(parserF).Ldloca(l.local)
                s.Call(tryReadFieldM)
            ) s

        //     new 'T(
        //         value1,
        //         // ...
        //         valueN
        //     )
        let s =
            locals
            |> Array.fold (fun s l ->
                ILStack.Ldloc(s, l.local).Reinterpret the<_>
            ) s
        s.Newobj(recordC).Reinterpret(the<stack<record>>).Ret()

    let defineParserType (dynamicModule: ModuleBuilder) recordType =
        let fields = FSharpType.GetRecordFields(recordType, allowAccessToPrivateRepresentation = true)
        let recordConstructor = FSharpValue.PreComputeRecordConstructorInfo(recordType, allowAccessToPrivateRepresentation = true)

        //[<Sealed>]
        //type DynamicJsonElementParsers.<namespace>.<guid>@<name> =
        //    inherit JsonElementParser<'T>

        let typeName = sprintf "DynamicJsonElementParsers.%s.%s@%s" recordType.Namespace (Guid.NewGuid().ToString "N") recordType.Name
        let baseT = typedefof<JsonElementParser<_>>.MakeGenericType recordType
        let parserT = dynamicModule.DefineType(typeName, T.Public ||| T.AutoClass ||| T.Sealed ||| T.BeforeFieldInit, baseT)

        let fieldParsers = [|
            for f in fields do
                // val private %fieldName: FSharpRecordFieldParser<%fieldType>
                let t = typedefof<FSharpRecordFieldParser<_>>.MakeGenericType(f.PropertyType)
                let cf = parserT.DefineField(f.Name, t, FieldAttributes.Private ||| FieldAttributes.InitOnly)
                {
                    parserField = cf
                    recordField = f
                }
        |]
        defineConstructor parserT fieldParsers
        defineParseMethod parserT fieldParsers recordConstructor
        parserT.CreateTypeInfo().AsType()

type FSharpRecordParserFactory() =
    inherit JsonElementParserFactory()

    let assemblyName = "DynamicJsonElementParsers" + Guid.NewGuid().ToString("N")
    let dynamicAssembly = AssemblyBuilder.DefineDynamicAssembly(AssemblyName assemblyName, AssemblyBuilderAccess.Run)
    let fileName = dynamicAssembly.GetName().Name + ".dll"
    let dynamicModule = dynamicAssembly.DefineDynamicModule fileName

    override _.CanParse t = FSharpType.IsRecord(t, allowAccessToPrivateRepresentation = true)
    override _.CreateParser(t, options) =
        let t = Emitter.defineParserType dynamicModule t
        t.GetConstructors().[0].Invoke [|options|] :?> JsonElementParser
