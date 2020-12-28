namespace LuaChecker.Primitives
open System.Diagnostics.CodeAnalysis

[<Struct>]
type The<'T> = | The

[<AutoOpen>]
module The =
    [<RequiresExplicitTypeArguments; GeneralizableValue>]
    let the<'T> : 'T The = The

type HEmpty = | HEmpty = 0uy

[<AutoOpen>]
module HEmpty =
    [<SuppressMessage("PublicUnusedMemberAnalyzer.fsx", "AA0001:MemberUnused")>]
    let (|HEmpty|) (x: HEmpty) = x
    let HEmpty = HEmpty.HEmpty

type IShape = interface end
module Shape =
    let instance (_: The<'Shape> when 'Shape :> IShape and 'Shape : struct) = Unchecked.defaultof<'Shape>
