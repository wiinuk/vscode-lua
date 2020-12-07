namespace LuaChecker.Primitives
open System
open System.Runtime.CompilerServices


type IUtf8SerializableShape<'R> =
    abstract Deserialize: utf8Bytes: byte ReadOnlySpan -> 'R

module Utf8Serializable =
    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let deserialize (_: The<'S> when 'S :> IUtf8SerializableShape<_> and 'S : struct) utf8Bytes = Unchecked.defaultof<'S>.Deserialize utf8Bytes
