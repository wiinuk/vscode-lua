namespace LuaChecker.Primitives

[<Struct>]
type The<'T> = | The

[<AutoOpen>]
module The =
    [<RequiresExplicitTypeArguments; GeneralizableValue>]
    let the<'T> : 'T The = The

type HEmpty = | HEmpty = 0uy

[<AutoOpen>]
module HEmpty =
    let (|HEmpty|) (x: HEmpty) = x
    let HEmpty = HEmpty.HEmpty

type IShape = interface end
module Shape =
    let instance (_: The<'Shape> when 'Shape :> IShape and 'Shape : struct) = Unchecked.defaultof<'Shape>
