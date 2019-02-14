namespace FSharp.Collections.Functorized.Internal

[<AutoOpen>]
module Wrapper =
  let inline wrap (a: 'a) : ^Wa =
    (^Wa: (static member Wrap: 'a -> ^Wa) a)

  let inline unwrap (a: ^Wa) =
    (^Wa: (static member Unwrap: ^Wa -> 'a) a)

  type OptimizedClosures.FSharpFunc<'a,'b,'c> with
    member inline this.InvokeTuple(a, b) =
      this.Invoke(a, b)
