namespace FSharp.Collections.Functorized
open System
open System.Collections.Generic

module Comparer =
  type Default =
    static member inline Compare (x: 't, y: 't) : int = compare x y

  type FromIComparer<'Comparer, 'T when 'Comparer :> IComparer<'T> and 'Comparer: (new: unit -> 'Comparer)>() =
    static let comparer = new 'Comparer()
    static member Compare (x: 'T, y: 'T) : int =
      comparer.Compare(x, y)

namespace FSharp.Collections.Functorized.Internal
  module Comparer =
    let inline compareBy (_: typrm< ^OrderedType >) x y =
      (^OrderedType: (static member Compare: _*_ -> int) x,y)

    let inline compareFstBy (_: typrm< ^OrderedType >) (x, _) (y, _) =
      (^OrderedType: (static member Compare: _*_ -> int) x,y)

