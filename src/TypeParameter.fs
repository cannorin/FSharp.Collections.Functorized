namespace FSharp.Collections.Functorized.Internal

[<AutoOpen>]
module TypeParameter =
  type typrm<'t> = struct end
  let inline typrm<'t> : typrm<'t> = Unchecked.defaultof<typrm<'t>>
  