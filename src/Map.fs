namespace FSharp.Collections.Functorized

namespace FSharp.Collections.Functorized.Internal
  open System.Collections.Generic
  open Tree
  open TreeImpl

  module MapImpl =
    let inline keyCmp (ty: typrm< ^Ord >) (x, _) (y, _) =
      Comparer.compareBy ty x y

    let inline uncurry (f: 'a -> 'b -> 'c) (a, b) = f a b

    let rec remove comp x t =
      match t with
        | Empty -> Empty
        | One (x', _) ->
          if comp x x' = 0 then Empty else t
        | Node ((xk', _) & x', l, r, _) ->
          let c = comp x xk'
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
        | Node ((x', _), l, r, _) ->
          let c = comp x x'
          if c < 0 then mem comp x l
          else c = 0 || mem comp x r
        | One (x', _) -> comp x x' = 0
        | Empty -> false

    let rec tryGetValue comparer k (v: byref<'value>) (m: Tree<'key * 'value>) = 
      match m with 
        | Empty -> false
        | One (k1, v1) -> 
          let c = comparer k k1
          if c = 0 then v <- v1; true
          else false
        | Node((k1, v1),l,r,_) -> 
          let c = comparer k k1
          if c < 0 then tryGetValue comparer k &v l
          elif c = 0 then v <- v1; true
          else tryGetValue comparer k &v r

    let inline find comparer k (m: Tree<'Key * 'Value>) =
      let mutable v = Unchecked.defaultof<'Value>
      if tryGetValue comparer k &v m then
        v
      else
        raise (KeyNotFoundException())

    let inline tryFind comparer k (m: Tree<'Key * 'Value>) =
      let mutable v = Unchecked.defaultof<'Value>
      if tryGetValue comparer k &v m then
        Some v
      else
        None

    let rec findKeyOpt (f:OptimizedClosures.FSharpFunc<_,_,_>) (outKey: byref<'key>) m = 
      match m with 
        | Empty -> false
        | One ((k, _) & kvp) ->
          if f.InvokeTuple kvp then outKey <- k; true
          else false
        | Node((k, _) & kvp,l,r,_) ->
          if f.InvokeTuple kvp then outKey <- k; true
          else
            findKeyOpt f &outKey l || findKeyOpt f &outKey r

    let inline findKey predicate (m: Tree<'Key * _>) =
      let mutable k = Unchecked.defaultof<'Key>
      if findKeyOpt (OptimizedClosures.FSharpFunc<_, _, _>.Adapt(predicate)) &k m then
        k
      else
        raise (KeyNotFoundException())

    let inline tryFindKey predicate (m: Tree<'Key * _>) =
      let mutable k = Unchecked.defaultof<'Key>
      if findKeyOpt (OptimizedClosures.FSharpFunc<_, _, _>.Adapt(predicate)) &k m then
        Some k
      else
        None

    let inline partition1 comparer (f:OptimizedClosures.FSharpFunc<_,_,_>) (kvp: _*_) (acc1, acc2) = 
      if f.InvokeTuple kvp then
        add comparer kvp acc1, acc2
      else
        acc1, add comparer kvp acc2
    
    let rec partitionAux comparer (f:OptimizedClosures.FSharpFunc<_,_,_>) s acc = 
      match s with 
        | Empty -> acc
        | One kvp -> partition1 comparer f kvp acc
        | Node (kvp,l,r,_) -> 
          let acc = partitionAux comparer f r acc 
          let acc = partition1 comparer f kvp acc
          partitionAux comparer f l acc

    let inline partition comparer f s = partitionAux comparer (OptimizedClosures.FSharpFunc<_,_,_>.Adapt(f)) s (empty,empty)

    let rec tryPickOpt (f:OptimizedClosures.FSharpFunc<_,_,_>) m =
      match m with 
        | Empty -> None
        | One kvp -> f.InvokeTuple kvp
        | Node (kvp,l,r,_) -> 
          match tryPickOpt f l with 
            | Some _ as res -> res 
            | None -> 
              match f.InvokeTuple kvp with 
                | Some _ as res -> res 
                | None -> 
                  tryPickOpt f r

    let inline tryPick f m = tryPickOpt (OptimizedClosures.FSharpFunc<_,_,_>.Adapt(f)) m

    let rec existsOpt (f:OptimizedClosures.FSharpFunc<_,_,_>) m = 
      match m with 
        | Empty -> false
        | One kvp -> f.InvokeTuple kvp
        | Node(kvp,l,r,_) -> existsOpt f l || f.InvokeTuple kvp || existsOpt f r

    let inline exists f m = existsOpt (OptimizedClosures.FSharpFunc<_,_,_>.Adapt(f)) m

    let rec forallOpt (f:OptimizedClosures.FSharpFunc<_,_,_>) m = 
      match m with 
        | Empty -> true
        | One kvp -> f.InvokeTuple kvp
        | Node(kvp,l,r,_) -> forallOpt f l && f.InvokeTuple kvp && forallOpt f r

    let inline forall f m = forallOpt (OptimizedClosures.FSharpFunc<_,_,_>.Adapt(f)) m

    let rec map f m = 
      match m with 
        | Empty -> empty
        | One(k,v) -> One(k,f k v)
        | Node((k,v),l,r,h) ->
          let l2 = map f l 
          let v2 = f k v 
          let r2 = map f r 
          Node((k,v2), l2, r2, h)

    let rec mapiOpt (f:OptimizedClosures.FSharpFunc<_,_,_>) m = 
      match m with
        | Empty -> empty
        | One(k,v) -> One(k, f.Invoke(k, v))
        | Node((k,v),l,r,h) -> 
          let l2 = mapiOpt f l 
          let v2 = f.Invoke(k,v)
          let r2 = mapiOpt f r 
          Node((k,v2), l2, r2, h)

    let inline mapi f m = mapiOpt (OptimizedClosures.FSharpFunc<_,_,_>.Adapt(f)) m

    let rec foldBackOpt (f:OptimizedClosures.FSharpFunc<_,_,_,_>) m x = 
      match m with 
        | Empty -> x
        | One(k,v) -> f.Invoke(k,v,x)
        | Node((k,v),l,r,_) -> 
          let x = foldBackOpt f r x
          let x = f.Invoke(k,v,x)
          foldBackOpt f l x

    let inline foldBack f m x = foldBackOpt (OptimizedClosures.FSharpFunc<_,_,_,_>.Adapt(f)) m x

    let rec foldOpt (f:OptimizedClosures.FSharpFunc<_,_,_,_>) x m  = 
      match m with 
        | Empty -> x
        | One(k,v) -> f.Invoke(x,k,v)
        | Node((k,v),l,r,_) -> 
          let x = foldOpt f x l
          let x = f.Invoke(x,k,v)
          foldOpt f x r

    let inline fold f x m = foldOpt (OptimizedClosures.FSharpFunc<_,_,_,_>.Adapt(f)) x m

    let inline foldSectionOpt comparer lo hi (f:OptimizedClosures.FSharpFunc<_,_,_,_>) m x =
      let rec foldFromTo (f:OptimizedClosures.FSharpFunc<_,_,_,_>) m x = 
        match m with 
          | Empty -> x
          | One(k,v) ->
            let cLoKey = comparer lo k
            let cKeyHi = comparer k hi
            let x = if cLoKey <= 0 && cKeyHi <= 0 then f.Invoke(k, v, x) else x
            x
          | Node((k,v),l,r,_) ->
            let cLoKey = comparer lo k
            let cKeyHi = comparer k hi
            let x = if cLoKey < 0                 then foldFromTo f l x else x
            let x = if cLoKey <= 0 && cKeyHi <= 0 then f.Invoke(k, v, x) else x
            let x = if cKeyHi < 0                 then foldFromTo f r x else x
            x
      if comparer lo hi = 1 then x else foldFromTo f m x

    let foldSection comparer lo hi f m x =
      foldSectionOpt comparer lo hi (OptimizedClosures.FSharpFunc<_,_,_,_>.Adapt(f)) m x

    let toList m = 
      let rec loop m acc = 
        match m with 
          | Empty -> acc
          | One kvp -> kvp::acc
          | Node(kvp,l,r,_) -> loop l (kvp::loop r acc)
      loop m []
    let inline toArray m = m |> toList |> Array.ofList
    let inline ofList comparer l = List.fold (fun acc kvp -> add comparer kvp acc) empty l

    let rec mkFromEnumerator comparer acc (e : IEnumerator<_>) = 
      if e.MoveNext() then 
        mkFromEnumerator comparer (add comparer e.Current acc) e
      else acc
      
    let inline ofArray comparer (arr : array<_>) =
      let mutable res = empty
      for kvp in arr do
        res <- add comparer kvp res 
      res

    let ofSeq comparer (c : seq<'Key * 'T>) =
      match c with 
        | :? array<'Key * 'T> as xs -> ofArray comparer xs
        | :? list<'Key * 'T> as xs -> ofList comparer xs
        | _ -> 
          use ie = c.GetEnumerator()
          mkFromEnumerator comparer empty ie 
      
    let copyToArray (s: Tree<_*_>) (arr: _[]) i =
      let j = ref i 
      s |> iter (fun (k,v) -> arr.[!j] <- KeyValuePair(k,v); j := !j + 1)

    // cannot be compared because 'ord contains the comparer which is obtained by SRTP
    [<CustomEquality; NoComparison; StructuredFormatDisplay("{AsString}")>]
    type FunctorizedMap<'key, 'value, 'ord when 'key: equality> = FunctorizedMap of Tree<'key * 'value> with
      static member inline Wrap x = FunctorizedMap x
      static member inline Unwrap (FunctorizedMap x) = x
      static member Equality (a: FunctorizedMap<_, _, 'ord>, b: FunctorizedMap<_, _, 'ord>) =
        use e1 = (toSeq <| unwrap a).GetEnumerator() 
        use e2 = (toSeq <| unwrap b).GetEnumerator() 
        let rec loop () = 
          let m1 = e1.MoveNext() 
          let m2 = e2.MoveNext()
          m1 = m2 && not m1 ||
            let (e1ck, e1cv) = e1.Current
            let (e2ck, e2cv) = e2.Current
            e1ck = e2ck && Unchecked.equals e1cv e2cv && loop()
        loop()
      member inline this.ChangeComparerTo<'ord2>() : FunctorizedMap<'key, 'value, 'ord2> =
        unwrap this |> wrap
      member this.ComputeHashCode() = 
        let inline combineHash x y = (x <<< 1) + y + 631 
        let mutable res = 0
        for k, v in this do
          res <- combineHash res (hash k)
          res <- combineHash res (Unchecked.hash v)
        abs res
      override this.GetHashCode() = this.ComputeHashCode()
      override this.Equals(that) = 
        match that with 
          | :? FunctorizedMap<'key, 'value, 'ord> as that -> 
            use e1 = (toSeq <| unwrap this).GetEnumerator() 
            use e2 = (toSeq <| unwrap that).GetEnumerator() 
            let rec loop () = 
              let m1 = e1.MoveNext() 
              let m2 = e2.MoveNext()
              m1 = m2 && not m1 ||
                let (e1ck, e1cv) = e1.Current
                let (e2ck, e2cv) = e2.Current
                e1ck = e2ck && Unchecked.equals e1cv e2cv && loop()
            loop()
          | _ -> false
      override x.ToString() =
        let tyName =
          sprintf "fmap<%s>" (typeof<'ord>.ToString())
        match List.ofSeq (Seq.truncate 4 x) with 
          | [] -> sprintf "%s []" tyName
          | [h1] -> System.Text.StringBuilder().Append(tyName).Append(" [").Append(sprintf "%A" h1).Append("]").ToString()
          | [h1;h2] -> System.Text.StringBuilder().Append(tyName).Append(" [").Append(sprintf "%A" h1).Append("; ").Append(sprintf "%A" h2).Append("]").ToString()
          | [h1;h2;h3] -> System.Text.StringBuilder().Append(tyName).Append(" [").Append(sprintf "%A" h1).Append("; ").Append(sprintf "%A" h2).Append("; ").Append(sprintf "%A" h3).Append("]").ToString()
          | h1 :: h2 :: h3 :: _ -> System.Text.StringBuilder().Append(tyName).Append(" [").Append(sprintf "%A" h1).Append("; ").Append(sprintf "%A" h2).Append("; ").Append(sprintf "%A" h3).Append("; ... ]").ToString() 
      member this.AsString = this.ToString()
      interface IEnumerable<'key * 'value> with
        member this.GetEnumerator() = (unwrap this :> IEnumerable<_>).GetEnumerator()
      interface System.Collections.IEnumerable with
        member this.GetEnumerator() = (unwrap this :> System.Collections.IEnumerable).GetEnumerator()

namespace FSharp.Collections.Functorized
  open System
  open System.Collections.Generic
  open FSharp.Collections.Functorized
  open FSharp.Collections.Functorized.Internal
  open Tree
  open TreeImpl
  open MapImpl

  type FunctorizedMap<'key, 'value, 'ord when 'key: equality> = MapImpl.FunctorizedMap<'key, 'value, 'ord>
  type fmap<'key, 'value, 'ord when 'key: equality> = FunctorizedMap<'key, 'value, 'ord>

  module Map =
    type Make<'ord> =
      static member inline changeComparerFrom (x: fmap<_, _, 'ord2>) : fmap<_, _, 'ord> = unwrap x |> wrap
      static member inline isEmpty (m: fmap<_, _, 'ord>) = isEmpty (unwrap m)
      static member inline containsKey key (m: fmap<_, _, ^OrderedType>) =
        mem (Comparer.compareBy typrm< ^OrderedType >) key (unwrap m)
      static member inline add key value (m: fmap<_, _, ^OrderedType>) : fmap<_, _, ^OrderedType> =
        unwrap m |> add (keyCmp typrm< ^OrderedType >) (key, value) |> wrap
      static member inline singleton x : fmap<_, _, 'ord> = One x |> wrap
      static member inline remove key (m: fmap<_, _, ^OrderedType>) : fmap<_, _, ^OrderedType> =
        unwrap m |> remove (Comparer.compareBy typrm< ^OrderedType >) key |> wrap
      static member inline count (m: fmap<_, _, 'ord>) = count (unwrap m)
      static member inline empty () : fmap<_, _, 'ord> = wrap Empty
      static member inline iter f (m: fmap<_, _, 'ord>) = iter (uncurry f) (unwrap m)
      static member inline forall predicate (m: fmap<_, _, 'ord>) = forall predicate (unwrap m)
      static member inline exists predicate (m: fmap<_, _, 'ord>) = exists predicate (unwrap m)
      static member inline filter predicate (m: fmap<_, _, ^OrderedType>) =
        filter (Comparer.compareBy typrm< ^OrderedType >) (uncurry predicate) (unwrap m)
      static member inline find key (m: fmap<_, _, ^OrderedType>) =
        find (Comparer.compareBy typrm< ^OrderedType >) key (unwrap m)
      static member inline tryFind key (m: fmap<_, _, ^OrderedType>) =
        tryFind (Comparer.compareBy typrm< ^OrderedType >) key (unwrap m)
      static member inline findKey predicate (m: fmap<_, _, 'ord>) = findKey predicate (unwrap m)
      static member inline tryFindKey predicate (m: fmap<_, _, 'ord>) = tryFindKey predicate (unwrap m)
      static member inline fold folder init (m: fmap<_, _, 'ord>) = fold folder init (unwrap m)
      static member inline foldSection lo hi folder init (m: fmap<_, _, ^OrderedType>) =
        foldSection (Comparer.compareBy typrm< ^OrderedType >) lo hi folder (unwrap m) init
      static member inline foldBack folder (m: fmap<_, _, 'ord>) init = foldBack folder (unwrap m) init
      static member inline map mapper (m: fmap<_, _, 'ord>) : fmap<_, _, 'ord> = mapi mapper (unwrap m) |> wrap
      static member inline partition predicate (m: fmap<_, _, ^OrderedType>) : fmap<_, _, ^OrderedType> * fmap<_, _, ^OrderedType> =
        let a, b = partition (keyCmp typrm< ^OrderedType >) predicate (unwrap m)
        wrap a, wrap b
      static member inline tryPick chooser (m: fmap<_, _, 'ord>) = tryPick chooser (unwrap m)
      static member inline pick chooser (m: fmap<_, _, 'ord>) = match tryPick chooser (unwrap m) with None -> raise (KeyNotFoundException()) | Some res -> res
      static member inline toArray (m: fmap<_, _, 'ord>) = toArray (unwrap m)
      static member inline toList (m: fmap<_, _, 'ord>)  = toList (unwrap m)
      static member inline toSeq (m: fmap<_, _, 'ord>)   = toSeq (unwrap m)
      static member inline appendList (xs: _ list) (m: fmap<_, _, ^OrderedType>) : fmap<_, _, ^OrderedType> =
        xs |> List.fold (fun m x -> add (keyCmp typrm< ^OrderedType >) x m) (unwrap m) |> wrap
      static member inline appendArray (xs: _[]) (m: fmap<_, _, ^OrderedType>) : fmap<_, _, ^OrderedType> =
        xs |> Array.fold (fun m x -> add (keyCmp typrm< ^OrderedType >) x m) (unwrap m) |> wrap
      static member inline appendSeq (xs: _ seq) (m: fmap<_, _, ^OrderedType>) : fmap<_, _, ^OrderedType> =
        xs |> Seq.fold (fun m x -> add (keyCmp typrm< ^OrderedType >) x m) (unwrap m) |> wrap

      // does not work since you cannnot extract comparer from non-SRTP 'ord
      [<System.Obsolete("Use empty() |> appendList xs.", true)>]
      static member inline ofList (xs: 'a list) : fset<'a, 'ord> = failwith "impossible"
      [<System.Obsolete("Use empty() |> appendArray xs.", true)>]
      static member inline ofArray (xs: 'a array) : fset<'a, 'ord> = failwith "impossible"
      [<System.Obsolete("Use empty() |> appendSeq xs.", true)>]
      static member inline ofSeq (xs: 'a seq) : fset<'a, 'ord> = failwith "impossible"

  type DefaultMap = Map.Make<Comparer.Default>
