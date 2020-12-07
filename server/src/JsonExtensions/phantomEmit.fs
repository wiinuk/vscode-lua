namespace LuaChecker.Quotations
open FSharp.Quotations
module E = Quotations.ExprShape
module E = Quotations.Patterns


module Expr =
    let rec tryPick (|Pick|_|) = function
        | Pick x -> Some x
        | E.ShapeCombination(_, es) -> List.tryPick (tryPick (|Pick|_|)) es
        | E.ShapeVar _ -> None
        | E.ShapeLambda(_, e) -> tryPick (|Pick|_|) e

    let findMethodDefinitionUntyped template =
        template
        |> tryPick (function
            | E.Call(_, m, _) -> Some m
            | E.PropertyGet(_, p, _) -> p.GetGetMethod() |> Some
            | E.PropertySet(_, p, _, _) -> p.GetSetMethod() |> Some
            | _ -> None
        )
        |> Option.map (fun m -> if m.IsGenericMethod then m.GetGenericMethodDefinition() else m)
        |> Option.defaultWith (fun _ -> failwithf "method not found: %A" template)

    let findMethodDefinition (template: Expr<_ -> _>) = findMethodDefinitionUntyped template


namespace LuaChecker.Reflection.Emit
open FSharp.Quotations
open LuaChecker.Primitives
open LuaChecker.Quotations
open System.Reflection
open System.Reflection.Emit
open System.Runtime.CompilerServices
type private C = Emit.OpCodes


type stack = unit
type stack<'T0> = stack * 'T0

type args = unit
type args<'Arg0> = 'Arg0 * args
type args<'Arg0,'Arg1> = 'Arg0 * args<'Arg1>
type args<'Arg0,'Arg1,'Arg2> = 'Arg0 * args<'Arg1,'Arg2>
type args<'Arg0,'Arg1,'Arg2,'Arg3> = 'Arg0 * args<'Arg1,'Arg2,'Arg3>
type args<'Arg0,'Arg1,'Arg2,'Arg3,'Arg4> = 'Arg0 * args<'Arg1,'Arg2,'Arg3,'Arg4>

type result = unit
type result<'Result> = result * 'Result

type pop<'Stack,'T0> = 'Stack * 'T0
type pop<'Stack,'T0,'T1> = pop<'Stack,'T0> * 'T1
type pop<'Stack,'T0,'T1,'T2> = pop<'Stack,'T0,'T1> * 'T2
type pop<'Stack,'T0,'T1,'T2,'T3> = pop<'Stack,'T0,'T1,'T2> * 'T3

type push<'Stack,'T0> = 'Stack * 'T0

[<Struct>]
type ILStack<'Stack,'Args,'Results> = ILStack of g: ILGenerator

[<Struct>]
type ILField<'This,'Field> = ILField of FieldInfo
module ILField =
    [<RequiresExplicitTypeArguments>]
    let declare<'This,'Field> f: ILField<'This,'Field> = ILField f

[<Struct>]
type ILMethod<'Args,'Results> = | ILMethod of MethodBase
module ILMethod =
    [<RequiresExplicitTypeArguments>]
    let declare<'Args,'Results> m: ILMethod<'Args,'Results> = ILMethod m

[<Struct>]
type ILLocal<'T> = ILLocal of LocalBuilder

[<Struct>]
type ILLabel<'Stack> = ILLabel of Label

[<AutoOpen>]
module private ILStackUtils =
    let emitCall (method: MethodBase) (g: ILGenerator) =
        match method with
        | null -> nullArg "g"
        | :? MethodInfo as m -> g.Emit(C.Call, m)
        | :? ConstructorInfo as c -> g.Emit(C.Call, c)
        | m -> failwithf "unknown method type: %A" m

[<Extension; Sealed; AbstractClass>]
type ILStack =

    /// ... => ..., string
    [<Extension>]
    static member Ldstr(ILStack g: ILStack<'Stack,'Args,'Results>, x: string): ILStack<push<'Stack,string>,'Args,'Results> =
        g.Emit(C.Ldstr, x)
        ILStack.ILStack g

    /// ... => ..., arg0
    [<Extension>]
    static member Ldarg_0(ILStack g: ILStack<'Stack,('Arg0 * 'Args),'Results>): ILStack<push<'Stack,'Arg0>,('Arg0 * 'Args),'Results> =
        g.Emit C.Ldarg_0
        ILStack.ILStack g

    /// ... => ..., arg1
    [<Extension>]
    static member Ldarg_1(ILStack g: ILStack<'Stack,'Arg0 * ('Arg1 * 'Args),'Results>): ILStack<push<'Stack,'Arg1>,'Arg0 * ('Arg1 * 'Args),'Results> =
        g.Emit C.Ldarg_1
        ILStack.ILStack g

    /// ... => ..., arg2
    [<Extension>]
    static member Ldarg_2(ILStack g: ILStack<'Stack,'Arg0 * ('Arg1 * ('Arg2 * 'Args)),'Results>): ILStack<push<'Stack,'Arg2>,'Arg0 * ('Arg1 * ('Arg2 * 'Args)),'Results> =
        g.Emit C.Ldarg_2
        ILStack.ILStack g

    /// ... => ..., arg2 byref
    [<Extension>]
    static member Ldarga_2(ILStack g: ILStack<'Stack,'Arg0 * ('Arg1 * ('Arg2 * 'Args)),'Results>): ILStack<push<'Stack,'Arg2>,'Arg0 * ('Arg1 * ('Arg2 * 'Args)),'Results> =
        g.Emit(C.Ldarga, 2s)
        ILStack.ILStack g

    /// ... => ..., arg3
    [<Extension>]
    static member Ldarg_3(ILStack g: ILStack<'Stack,'Arg0 * ('Arg1 * ('Arg2 * ('Arg3 * 'Args))),'Results>): ILStack<push<'Stack,'Arg3>,'Arg0 * ('Arg1 * ('Arg2 * ('Arg3 * 'Args))),'Results> =
        g.Emit C.Ldarg_3
        ILStack.ILStack g

    /// ... => ..., this
    [<Extension>]
    static member Newobj(ILStack g: ILStack<'Stack,'Args,'Results>, ILMethod method: ILMethod<args<'This>, result>): ILStack<push<'Stack,'This>,'Args,'Results> =
        g.Emit(C.Newobj, method :?> ConstructorInfo)
        ILStack.ILStack g

    /// ..., this => ...
    [<Extension>]
    static member Call'(ILStack g: ILStack<pop<'Stack,'This>,'Args,'Results>, method: Expr<'This -> unit -> unit>): ILStack<'Stack,'Args,'Results> =
        g.Emit(C.Call, Expr.findMethodDefinition method)
        ILStack.ILStack g

    /// ..., arg1 => ...
    [<Extension>]
    static member Call(ILStack g: ILStack<pop<'Stack,'Arg1>,'Args,'Results>, ILMethod method: ILMethod<args<'Arg1>, unit>): ILStack<'Stack,'Args,'Results> =
        emitCall method g
        ILStack.ILStack g

    /// ..., arg1, arg2, arg3, arg4 => ...
    [<Extension>]
    static member Call(ILStack g: ILStack<pop<'Stack,'Arg1,'Arg2,'Arg3,'Arg4>,'Args,'Results>, ILMethod method: ILMethod<args<'Arg1,'Arg2,'Arg3,'Arg4>, result>): ILStack<'Stack,'Args,'Results> =
        emitCall method g
        ILStack.ILStack g

    /// ..., arg1 => ..., result
    [<Extension>]
    static member Call(ILStack g: ILStack<pop<'Stack,'Arg1>,'Args,'Results>, ILMethod method: ILMethod<args<'Arg1>,result<'Result>>): ILStack<push<'Stack,'Result>,'Args,'Results> =
        emitCall method g
        ILStack.ILStack g

    /// ..., arg1, arg2 => ..., result
    [<Extension>]
    static member Call(ILStack g: ILStack<pop<'Stack,'Arg1,'Arg2>,'Args,'Results>, ILMethod method: ILMethod<args<'Arg1,'Arg2>,result<'Result>>): ILStack<push<'Stack,'Result>,'Args,'Results> =
        emitCall method g
        ILStack.ILStack g

    /// ..., arg1, arg2, arg3, arg4 => ..., result
    [<Extension>]
    static member Call(ILStack g: ILStack<pop<'Stack,'Arg1,'Arg2,'Arg3,'Arg4>,'Args,'Results>, ILMethod method: ILMethod<args<'Arg1,'Arg2,'Arg3,'Arg4>, result<'Result>>): ILStack<push<'Stack,'Result>,'Args,'Results> =
        emitCall method g
        ILStack.ILStack g

    /// ..., this => ..., field
    [<Extension>]
    static member Ldfld(ILStack g: ILStack<pop<'Stack,'This>,'Args,'Results>, ILField f: ILField<'This,'Field>): ILStack<push<'Stack,'Field>,'Args,'Results> =
        g.Emit(C.Ldfld, f)
        ILStack.ILStack g

    /// ..., this, field => ...
    [<Extension>]
    static member Stfld(ILStack g: ILStack<pop<'Stack,'This,'Field>,'Args,'Results>, ILField f: ILField<'This,'Field>): ILStack<'Stack,'Args,'Results> =
        g.Emit(C.Stfld, f)
        ILStack.ILStack g

    [<Extension>]
    static member MarkLabel(ILStack g: ILStack<'Stack,'Args,'Results>, ILLabel l: ILLabel<'Stack>): ILStack<'Stack,'Args,'Results> =
        g.MarkLabel l
        ILStack.ILStack g

    [<Extension>]
    static member DefineLabel(ILStack g): ILLabel<'Stack> = ILLabel <| g.DefineLabel()

    /// ..., boolean => ...
    [<Extension>]
    static member Brfalse(ILStack g: ILStack<pop<'Stack, bool>,'Args,'Results>, ILLabel l: ILLabel<'Stack>): ILStack<'Stack,'Args,'Results> =
        g.Emit(C.Brfalse, l)
        ILStack.ILStack g

    /// ..., boolean => ...
    [<Extension>]
    static member Brtrue(ILStack g: ILStack<pop<'Stack, bool>,'Args,'Results>, ILLabel l: ILLabel<'Stack>): ILStack<'Stack,'Args,'Results> =
        g.Emit(C.Brtrue, l)
        ILStack.ILStack g

    /// ..., ...
    [<Extension>]
    static member Br(ILStack g: ILStack<'Stack,'Args,'Results>, ILLabel l: ILLabel<'Stack>): ILStack<'Stack,'Args,'Results> =
        g.Emit(C.Br, l)
        ILStack.ILStack g

    [<Extension>]
    static member DeclareLocal(ILStack g, _: The<'Local>, t): ILLocal<'Local> = ILLocal.ILLocal <| g.DeclareLocal t

    /// ... => ..., local
    [<Extension>]
    static member Ldloc(ILStack g: ILStack<'Stack,'Args,'Results>, ILLocal l: ILLocal<'Local>): ILStack<push<'Stack,'Local>,'Args,'Results> =
        g.Emit(C.Ldloc, l)
        ILStack.ILStack g

    /// ... => ..., local byref
    [<Extension>]
    static member Ldloca(ILStack g: ILStack<'Stack,'Args,'Results>, ILLocal l: ILLocal<'Local>): ILStack<push<'Stack,'Local>,'Args,'Results> =
        g.Emit(C.Ldloca, l)
        ILStack.ILStack g

    /// ..., results... => ...
    [<Extension>]
    static member Ret(ILStack g: ILStack<'Results,'Args,'Results>) = g.Emit C.Ret

    [<Extension>]
    static member Reinterpret(ILStack g: ILStack<_,'Args,'Results>, _: The<'NewStack>): ILStack<'NewStack,'Args,'Results> = ILStack.ILStack g

module ILStack =
    [<RequiresExplicitTypeArguments>]
    let declare<'Stack,'Args,'Results> g : ILStack<'Stack,'Args,'Results> = ILStack.ILStack g

    [<RequiresExplicitTypeArguments>]
    let getILGenerator<'Args,'Results> (m: MethodBuilder): ILStack<stack,'Args,'Results> =
        declare<stack,'Args,'Results> <| m.GetILGenerator()
