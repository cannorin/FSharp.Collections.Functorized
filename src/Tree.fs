namespace FSharp.Collections.Functorized.Internal
open System.Collections.Generic

module Tree =
  [<CompilationRepresentation(CompilationRepresentationFlags.UseNullAsTrueValue)>]
  [<NoEquality; NoComparison>]
  type Tree<'a> =
    | Empty
    | One of 'a
    | Node of 'a * Tree<'a> * Tree<'a> * int
    static member internal ToSeq this =
      let rec iter this =
        seq {
          match this with
            | Empty -> ()
            | One x -> yield x
            | Node (x, l, r, _) ->
              yield! iter l
              yield x
              yield! iter r
        }
      iter this
    interface IEnumerable<'a> with
      member this.GetEnumerator() = (Tree<_>.ToSeq this).GetEnumerator()
    interface System.Collections.IEnumerable with
      member this.GetEnumerator() = (Tree<_>.ToSeq this).GetEnumerator() :> _
  
  [<Literal>]
  let tolerance = 2

  module TreeImpl =
    let rec countAux s acc = 
      match s with 
      | Node (_,l,r,_) -> countAux l (countAux r (acc+1))
      | One(_) -> acc+1
      | Empty -> acc           
    let count s = countAux s 0
    let singleton x = One x
    let empty<'a> : Tree<'a> = Empty
    let height tree =
      match tree with Empty -> 0 | One _ -> 1 | Node (_,_,_,h) -> h
    let mk l x r =
      match l, r with
        | Empty, Empty -> One x
        | _ ->
          let hl = height l
          let hr = height r
          let m =
            if hr > hl + tolerance then hr else hl
          Node (x, l, r, m+1)
    let rebalance l x r =
      let hl = height l
      let hr = height r
      if hr > hl + tolerance then
        match r with
          | Node (x', l', r', _) ->
            if height l' > hl + 1 then
              match l' with
                | Node (x'', l'', r'', _) ->
                  mk (mk l x l'') x'' (mk r'' x' r')
                | _ -> failwith "rebalance"
            else
              mk (mk l x l') x' r'
          | _ -> failwith "rebalance"
      else
        if hl > hr + tolerance then
          match l with
            | Node (x', l', r', _) ->
              if height r' > hr + 1 then
                match r' with
                  | Node (x'', l'', r'', _) ->
                    mk (mk l' x' l'') x'' (mk r'' x r)
                  | _ -> failwith "rebalance"
              else
                mk l' x' (mk r' x r)
            | _ -> failwith "rebalance"
        else
          Node (x, l, r, if hl >= hr then hl+1 else hr+1)
    let rec add comp x t =
      match t with
        | Empty -> One x
        | One x' ->
          let c = comp x x'
          if c < 0 then Node (x, Empty, t, 2)
          else if c = 0 then One x
          else Node (x, t, Empty, 2)
        | Node (x', l, r, h) ->
          let c = comp x x'
          if c < 0 then rebalance (add comp x l) x' r
          else if c = 0 then Node (x, l, r, h)
          else rebalance l x' (add comp x r)
    let rec spliceOutSucc t =
      match t with
        | Empty -> failwith "spliceOutSucc"
        | One x -> (x, Empty)
        | Node (x, l, r, _) ->
          match l with
            | Empty -> (x, r)
            | _ ->
              let (x', l') = spliceOutSucc l
              (x', mk l' x' r)
    let rec remove comp x t =
      match t with
        | Empty -> Empty
        | One x' ->
          if comp x x' = 0 then Empty else t
        | Node (x', l, r, _) ->
          let c = comp x x'
          if c < 0 then rebalance (remove comp x l) x' r
          else if c = 0 then
            match l, r with
              | Empty, _ -> l | _, Empty -> r
              | _ ->
                let (x', r') = spliceOutSucc r
                mk l x' r'
          else rebalance l x' (remove comp x r)
    let rec mem comp x t =
      match t with
        | Node (x', l, r, _) ->
          let c = comp x x'
          if c < 0 then mem comp x l
          else c = 0 || mem comp x r
        | One x' -> comp x x' = 0
        | Empty -> false
    let rec iter f t =
      match t with
        | Node (x, l, r, _) -> iter f l; f x; iter f r
        | One x -> f x
        | Empty -> ()
    let rec private foldBackOpt (f: OptimizedClosures.FSharpFunc<_,_,_>) tree x =
      match tree with
        | Node (k, l, r, _) -> foldBackOpt f l (f.Invoke(k, foldBackOpt f r x))
        | One k -> f.Invoke(k, x)
        | Empty -> x
    let foldBack f m x = foldBackOpt (OptimizedClosures.FSharpFunc<_, _, _>.Adapt(f)) m x
    let rec private foldOpt (f: OptimizedClosures.FSharpFunc<_, _, _>) x tree =
      match tree with
        | Node (k, l, r, _) -> foldOpt f (f.Invoke(foldOpt f x l, k)) r
        | One k -> f.Invoke(x, k)
        | Empty -> x
    let fold f x m = foldOpt (OptimizedClosures.FSharpFunc<_,_,_>.Adapt(f)) x m
    let rec forall predicate tree =
      match tree with
        | Node (k, l, r, _) -> predicate k && forall predicate l && forall predicate r
        | One k -> predicate k
        | Empty -> true
    let rec exists predicate tree =
      match tree with
        | Node (k, l, r, _) -> predicate k || exists predicate l || exists predicate r
        | One k -> predicate k
        | Empty -> false
    let isEmpty tree = match tree with Empty -> true | _ -> false
    let rec filterAux comp predicate tree acc = 
      match tree with 
      | Node (k,l,r,_) -> 
        let acc = if predicate k then add comp k acc else acc 
        filterAux comp predicate l (filterAux comp predicate r acc)
      | One k -> if predicate k then add comp k acc else acc
      | Empty -> acc           
    let filter comp predicate tree = filterAux comp predicate tree empty
    let map comp f tree =
      tree |> fold (fun acc k -> add comp (f k) acc) empty
    let toSeq (tree: Tree<_>) = Tree<_>.ToSeq tree

