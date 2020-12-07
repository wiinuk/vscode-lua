namespace LuaChecker.Text.Json.Serialization
open FSharp.Reflection
open System
open System.Reflection
open System.Reflection.Emit
open System.Text.Json.Serialization


type JsonFSharpRecordConverter() =
    inherit JsonConverterFactory()

    let assemblyName = AssemblyName "DynamicAssembly"
    #if NET461
    let dynamicAssembly = AppDomain.CurrentDomain.DefineDynamicAssembly(assemblyName, AssemblyBuilderAccess.RunAndSave)
    let fileName = dynamicAssembly.GetName().Name + ".dll"
    let dynamicModule = dynamicAssembly.DefineDynamicModule(fileName, fileName, emitSymbolInfo = true)
    #else
    let dynamicAssembly = AssemblyBuilder.DefineDynamicAssembly(assemblyName, AssemblyBuilderAccess.Run)
    let fileName = dynamicAssembly.GetName().Name + ".dll"
    let dynamicModule = dynamicAssembly.DefineDynamicModule fileName
    #endif

    override _.CanConvert typeToConvert = FSharpType.IsRecord(typeToConvert, allowAccessToPrivateRepresentation = true)
    override _.CreateConverter(typeToConvert, options) =
        let t = JsonFSharpRecordConverterEmitter.defineConverterType dynamicModule typeToConvert
        t.GetConstructors().[0].Invoke [|options|] :?> JsonConverter
