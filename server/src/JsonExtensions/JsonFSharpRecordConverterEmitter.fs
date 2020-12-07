module internal LuaChecker.Text.Json.Serialization.JsonFSharpRecordConverterEmitter
open FSharp.Reflection
open LuaChecker.Primitives
open LuaChecker.Reflection.Emit
open LuaChecker.Quotations
open LuaChecker.Text.Json.Serialization.Internal
open System
open System.IO
open System.Reflection
open System.Reflection.Emit
open System.Text.Json
open System.Text.Json.Serialization


[<AutoOpen>]
module private Privates =
    type field = class end
    type record = class end
    type converter = record JsonConverter
    type _Utf8JsonReader = class end

    type C = Emit.OpCodes
    type M = Reflection.MethodAttributes
    type B = Reflection.BindingFlags
    type T = Reflection.TypeAttributes

type RecordBuilderInfo = {
    recordField: PropertyInfo
    converterField: FieldBuilder
}

let defineConstructor (converterT: TypeBuilder) fieldConverters =
    let createFieldMD1 = Expr.findMethodDefinition <@ JsonConverterFSharpRecord.createField<_> @>

    // new (options: JsonSerializerOptions) = {
    //     field1 = JsonConverterFSharpRecord.createField<"<field1Type>"> "<field1Name>" options
    //     ...
    //     fieldN = JsonConverterFSharpRecord.createField<"<fieldNType>"> "<fieldNName>" options
    // }
    let constructor = converterT.DefineConstructor(M.Public, CallingConventions.Standard, [|typeof<JsonSerializerOptions>|])
    constructor.DefineParameter(1, ParameterAttributes.None, "options") |> ignore

    let baseC =
        converterT.BaseType.GetConstructor(B.Instance ||| B.NonPublic ||| B.Public, null, Type.EmptyTypes, null)
        |> ILMethod.declare<args<converter>, result>
    let s = constructor.GetILGenerator() |> ILStack.declare<stack, args<converter, JsonSerializerOptions>, result>

    let s = s.Ldarg_0().Call(baseC)
    let s =
        fieldConverters
        |> Array.fold (fun s f ->
            let createFieldM =
                createFieldMD1.MakeGenericMethod f.recordField.PropertyType
                |> ILMethod.declare<args<string, JsonSerializerOptions>, result<FSharpRecordFieldConverter<field>>>

            let converterF = f.converterField |> ILField.declare<converter, FSharpRecordFieldConverter<field>>

            let s = ILStack.Ldarg_0(s).Ldstr(f.recordField.Name).Ldarg_1().Call(createFieldM).Stfld(converterF)
            s
        ) s

    s.Ret()

let defineReadMethod (converterT: TypeBuilder) fieldConverters recordConstructor =
    let recordC = ILMethod.declare<args<record>, result> recordConstructor

    // override this.Read(reader: Utf8JsonReader byref, typeToConvert: Type, options: JsonSerializerOptions): 'RecordType =
    let baseReadM = converterT.BaseType.GetMethod "Read"
    let readM = converterT.DefineMethod(baseReadM.Name, M.Public ||| M.Virtual ||| M.HideBySig, baseReadM.ReturnType, [| for p in baseReadM.GetParameters() -> p.ParameterType |])
    for p in baseReadM.GetParameters() do
        readM.DefineParameter(p.Position + 1, p.Attributes, p.Name) |> ignore

    let readStartRecordM =
        typeof<JsonConverterFSharpRecord.Marker>.DeclaringType.GetMethod "readStartRecord"
        |> ILMethod.declare<args<_Utf8JsonReader>, result>

    let s = ILStack.getILGenerator<args<converter, _Utf8JsonReader, Type, JsonSerializerOptions>, result<record>> readM

    //    let mutable value1 = Unchecked.defaultof<_>
    //    // ...
    //    let mutable valueN = Unchecked.defaultof<_>
    let locals = [|
        for f in fieldConverters ->
            let local = s.DeclareLocal(the<field>, f.recordField.PropertyType)
            {| local = local; converter = f |}
    |]

    //    JsonConverterFSharpRecord.readStartRecord &reader
    let s = s.Ldarg_1().Call(readStartRecordM)

    //    beginLoop:
    //        ifFalse (readIsPropertyWithVerify &reader) then goto endLoop
    //
    //        if (tryReadField &reader options this.field1 &value1) then goto beginLoop
    //        // ...
    //        if (tryReadField &reader options this.fieldN &valueN) then goto beginLoop
    //
    //        skipAnyProperty &reader
    //        goto beginLoop
    //    endLoop:
    let readIsPropertyWithVerifyM =
        typeof<JsonConverterFSharpRecord.Marker>.DeclaringType.GetMethod "readIsPropertyWithVerify"
        |> ILMethod.declare<args<_Utf8JsonReader>, result<bool>>
    let tryReadFieldMD1 = typeof<JsonConverterFSharpRecord.Marker>.DeclaringType.GetMethod "tryReadField"
    let skipAnyPropertyM = typeof<JsonConverterFSharpRecord.Marker>.DeclaringType.GetMethod "skipAnyProperty" |> ILMethod.declare<args<_Utf8JsonReader>, result>
    let beginLoopL = s.DefineLabel()
    let endLoopL = s.DefineLabel()
    let s = s.MarkLabel beginLoopL
    let s = s.Ldarg_1().Call(readIsPropertyWithVerifyM).Brfalse(endLoopL)
    let s =
        locals
        |> Array.fold (fun s l ->
            let tryReadFieldM =
                tryReadFieldMD1.MakeGenericMethod l.converter.recordField.PropertyType
                |> ILMethod.declare<args<_Utf8JsonReader, JsonSerializerOptions, FSharpRecordFieldConverter<field>, field>, result<bool>>

            let converterF =
                l.converter.converterField
                |> ILField.declare<converter, FSharpRecordFieldConverter<field>>

            let s = ILStack.Ldarg_1(s).Ldarg_3().Ldarg_0().Ldfld(converterF).Ldloca(l.local)
            s.Call(tryReadFieldM).Brtrue(beginLoopL)
        ) s
    let s = s.Ldarg_1().Call(skipAnyPropertyM).Br(beginLoopL)
    let s = s.MarkLabel endLoopL

    //    new 'RecordType(
    //        value1,
    //        // ...
    //        valueN
    //    )
    let s =
        locals
        |> Array.fold (fun s l ->
            ILStack.Ldloc(s, l.local).Reinterpret the<_>
        ) s
    s.Newobj(recordC).Reinterpret(the<stack<record>>).Ret()

let defineWriteMethod (converterT: TypeBuilder) fieldConverters =
    // override this.Write(writer: Utf8JsonWriter, record: 'RecordType, options: JsonWriterOptions) =
    let baseWriteM = converterT.BaseType.GetMethod "Write"
    let readM = converterT.DefineMethod(baseWriteM.Name, M.Public ||| M.Virtual ||| M.HideBySig, baseWriteM.ReturnType, [| for p in baseWriteM.GetParameters() -> p.ParameterType |])
    for m in baseWriteM.GetParameters() do
        readM.DefineParameter(m.Position + 1, m.Attributes, m.Name) |> ignore

    let s = ILStack.getILGenerator<args<converter, Utf8JsonWriter, record, JsonWriterOptions>, result> readM

    //    writer.WriteStartObject()
    let s = s.Ldarg_1().Call'<@ fun w -> w.WriteStartObject @>

    let writeFieldMD1 = Expr.findMethodDefinition <@ JsonConverterFSharpRecord.writeField<_> @>
    let s =
        fieldConverters
        |> Array.fold (fun s f ->
            let getFieldM = ILMethod.declare<args<record>, result<field>> (f.recordField.GetGetMethod())
            let writeFieldM = writeFieldMD1.MakeGenericMethod f.recordField.PropertyType
            let writeFieldM = ILMethod.declare<args<Utf8JsonWriter, FSharpRecordFieldConverter<field>, field, JsonWriterOptions>, result> writeFieldM
            let converterF = ILField.declare<converter, FSharpRecordFieldConverter<field>> f.converterField

            // JsonConverterFSharpRecord.writeField writer this.fieldN record.fieldN options
            let s = ILStack.Ldarg_1(s).Ldarg_0().Ldfld converterF
            let s = if f.recordField.DeclaringType.IsValueType then s.Ldarga_2() else s.Ldarg_2()
            let s = s.Call(getFieldM).Ldarg_3().Call(writeFieldM)
            s
        ) s

    s.Ldarg_1().Call'(<@ fun w -> w.WriteEndObject @>).Ret()

let defineConverterType (dynamicModule: ModuleBuilder) recordType =
    let fields = FSharpType.GetRecordFields(recordType, allowAccessToPrivateRepresentation = true)
    let recordConstructor = FSharpValue.PreComputeRecordConstructorInfo(recordType, allowAccessToPrivateRepresentation = true)

    // type DynamicJsonConverters.<namespace>.<guid>@<name> =
    //     inherit JsonConverter<'recordType>
    let converterTypeName = sprintf "DynamicJsonConverters.%s.%s@%s" recordType.Namespace (Guid.NewGuid().ToString "N") recordType.Name
    let baseT = typedefof<JsonConverter<_>>.MakeGenericType recordType
    let converterT = dynamicModule.DefineType(converterTypeName, T.Public ||| T.AutoClass ||| T.Sealed ||| T.BeforeFieldInit, baseT)

    let fieldConverters = [|
        for f in fields do
            // val private %fieldName : FSharpRecordFieldConverter<%fieldType>
            let t = typedefof<FSharpRecordFieldConverter<_>>.MakeGenericType(f.PropertyType)
            let cf = converterT.DefineField(f.Name, t, FieldAttributes.Private ||| FieldAttributes.InitOnly)
            {
                converterField = cf
                recordField = f
            }
    |]
    defineConstructor converterT fieldConverters
    defineReadMethod converterT fieldConverters recordConstructor
    defineWriteMethod converterT fieldConverters
    converterT.CreateTypeInfo().AsType()
