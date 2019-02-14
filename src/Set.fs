namespace FSharp.Collections.Functorized

namespace FSharp.Collections.Functorized.Internal
  open System.Collections.Generic
  open Tree
  open TreeImpl
  module SetImpl =
    let rec balance comparer t1 k t2 =
      // Given t1 < k < t2 where t1 and t2 are "balanced",
      // return a balanced tree for <t1,k,t2>.
      // Recall: balance means subtrees heights differ by at most "tolerance"
      match t1,t2 with
        | Empty,t2  -> add comparer k t2 // drop t1 = empty 
        | t1,Empty  -> add comparer k t1 // drop t2 = empty 
        | One k1,t2 -> add comparer k (add comparer k1 t2)
        | t1,One k2 -> add comparer k (add comparer k2 t1)
        | Node (k1,t11,t12,h1),Node (k2,t21,t22,h2) ->
          // Have:  (t11 < k1 < t12) < k < (t21 < k2 < t22)
          // Either (a) h1,h2 differ by at most 2 - no rebalance needed.
          //        (b) h1 too small, i.e. h1+2 < h2
          //        (c) h2 too small, i.e. h2+2 < h1 
          if   h1+tolerance < h2 then
            // case: b, h1 too small 
            // push t1 into low side of t2, may increase height by 1 so rebalance 
            rebalance (balance comparer t1 k t21) k2 t22
          elif h2+tolerance < h1 then
            // case: c, h2 too small 
            // push t2 into high side of t1, may increase height by 1 so rebalance 
            rebalance t11 k1 (balance comparer t12 k t2)
          else
            // case: a, h1 and h2 meet balance requirement 
            mk t1 k t2
    let rec split comparer pivot t =
      // Given a pivot and a set t
      // Return { x in t s.t. x < pivot }, pivot in t? , { x in t s.t. x > pivot } 
      match t with
        | Node (k1,t11,t12,_) ->
            let c = comparer pivot k1
            if   c < 0 then // pivot t1 
                let t11Lo,havePivot,t11Hi = split comparer pivot t11
                t11Lo,havePivot, balance comparer t11Hi k1 t12
            elif c = 0 then // pivot is k1 
                t11,true,t12
            else            // pivot t2 
                let t12Lo,havePivot,t12Hi = split comparer pivot t12
                balance comparer t11 k1 t12Lo,havePivot,t12Hi
        | One k1 ->
            let c = comparer k1 pivot
            if   c < 0 then t       ,false,Empty // singleton under pivot 
            elif c = 0 then Empty,true ,Empty // singleton is    pivot 
            else            Empty,false,t        // singleton over  pivot 
        | Empty  -> Empty,false,Empty
    let subset comparer a b  = forall (fun x -> mem comparer x b) a
    let psubset comparer a b  = forall (fun x -> mem comparer x b) a && exists (fun x -> not (mem comparer x a)) b
    let rec diffAux comparer m acc = 
      match acc with
        | Empty -> acc
        | _ ->
          match m with 
            | Node (k,l,r,_) -> diffAux comparer l (diffAux comparer r (remove comparer k acc))
            | One(k) -> remove comparer k acc
            | Empty -> acc           
    let diff comparer a b = diffAux comparer b a
    let rec union comparer t1 t2 =
      match t1,t2 with               
        | Node (k1,t11,t12,h1),Node (k2,t21,t22,h2) -> // (t11 < k < t12) AND (t21 < k2 < t22) 
          // Divide and Conquer:
          //   Suppose t1 is largest.
          //   Split t2 using pivot k1 into lo and hi.
          //   Union disjoint subproblems and then combine. 
          if h1 > h2 then
            let lo,_,hi = split comparer k1 t2 in
            balance comparer (union comparer t11 lo) k1 (union comparer t12 hi)
          else
            let lo,_,hi = split comparer k2 t1 in
            balance comparer (union comparer t21 lo) k2 (union comparer t22 hi)
        | Empty,t -> t
        | t,Empty -> t
        | One k1,t2 -> add comparer k1 t2
        | t1,One k2 -> add comparer k2 t1
    let rec intersectionAux comparer b m acc = 
      match m with 
        | Node (k,l,r,_) -> 
          let acc = intersectionAux comparer b r acc 
          let acc = if mem comparer k b then add comparer k acc else acc 
          intersectionAux comparer b l acc
        | One(k) -> 
          if mem comparer k b then add comparer k acc else acc
        | Empty -> acc
    let intersection comparer a b = intersectionAux comparer b a Empty
    let partition1 comparer f k (acc1,acc2) = if f k then (add comparer k acc1,acc2) else (acc1,add comparer k acc2) 
    let rec partitionAux comparer f s acc = 
      match s with 
        | Node (k,l,r,_) -> 
          let acc = partitionAux comparer f r acc 
          let acc = partition1 comparer f k acc
          partitionAux comparer f l acc
        | One(k) -> partition1 comparer f k acc
        | Empty -> acc           
    let partition comparer f s = partitionAux comparer f s (Empty,Empty)
    let (|MatchNode|MatchEmpty|) s = 
      match s with 
        | Node (k2,l,r,_) -> MatchNode (k2,l,r)
        | One(k2) -> MatchNode (k2,Empty,Empty)
        | Empty -> MatchEmpty
    let rec minimumElementAux s n = 
      match s with 
        | Node (k,l,_,_) -> minimumElementAux l k
        | One(k) -> k
        | Empty -> n
    and minimumElementOpt s = 
      match s with 
        | Node (k,l,_,_) -> Some(minimumElementAux l k)
        | One(k) -> Some k
        | Empty -> None
    and maximumElementAux s n = 
      match s with 
        | Node (k,_,r,_) -> maximumElementAux r k
        | One(k) -> k
        | Empty -> n             
    and maximumElementOpt s = 
      match s with 
        | Node (k,_,r,_) -> Some(maximumElementAux r k)
        | One(k) -> Some(k)
        | Empty -> None
    let minimumElement s = 
      match minimumElementOpt s with 
        | Some(k) -> k
        | None -> invalidArg "s" "tree is empty"
    let maximumElement s = 
      match maximumElementOpt s with 
        | Some(k) -> k
        | None -> invalidArg "s" "tree is empty"
    let rec compareStacks comparer l1 l2 =
      match l1,l2 with 
        | [],[] ->  0
        | [],_  -> -1
        | _ ,[] ->  1
        | (Empty  _ :: t1),(Empty    :: t2) -> compareStacks comparer t1 t2
        | (One(n1k) :: t1),(One(n2k) :: t2) -> 
          let c = comparer n1k n2k
          if c <> 0 then c else compareStacks comparer t1 t2
        | (One(n1k) :: t1),(Node (n2k,Empty,n2r,_) :: t2) -> 
          let c = comparer n1k n2k
          if c <> 0 then c else compareStacks comparer (Empty :: t1) (n2r :: t2)
        | (Node (n1k,(Empty as emp),n1r,_) :: t1),(One(n2k) :: t2) -> 
          let c = comparer n1k n2k
          if c <> 0 then c else compareStacks comparer (n1r :: t1) (emp :: t2)
        | (Node (n1k,Empty,n1r,_) :: t1),(Node (n2k,Empty,n2r,_) :: t2) -> 
          let c = comparer n1k n2k
          if c <> 0 then c else compareStacks comparer (n1r :: t1) (n2r :: t2)
        | (One(n1k) :: t1),_ -> 
          compareStacks comparer (Empty :: One(n1k) :: t1) l2
        | (Node (n1k,n1l,n1r,_) :: t1),_ -> 
          compareStacks comparer (n1l :: Node (n1k,Empty,n1r,0) :: t1) l2
        | _,(One(n2k) :: t2) -> 
          compareStacks comparer l1 (Empty :: One(n2k) :: t2)
        | _,(Node (n2k,n2l,n2r,_) :: t2) -> 
          compareStacks comparer l1 (n2l :: Node (n2k,Empty,n2r,0) :: t2)
    let compare comparer s1 s2 = 
      match s1,s2 with 
        | Empty,Empty -> 0
        | Empty,_ -> -1
        | _,Empty -> 1
        | _ -> compareStacks comparer [s1] [s2]
    let choose s = minimumElement s
    let toList s = 
      let rec loop m acc = 
        match m with 
          | Node (k,l,r,_) -> loop l (k :: loop r acc)
          | One(k) ->  k ::acc
          | Empty -> acc
      loop s []
    let copyToArray s (arr: _[]) i =
      let j = ref i 
      iter (fun x -> arr.[!j] <- x; j := !j + 1) s
    let toArray s = 
      let n = (count s) 
      let res = Array.zeroCreate n 
      copyToArray s res 0;
      res
    let rec mkFromEnumerator comparer acc (e: IEnumerator<_>) = 
      if e.MoveNext() then 
        mkFromEnumerator comparer (add comparer e.Current acc) e
      else acc
    let ofSeq comparer (c: IEnumerable<_>) =
      use ie = c.GetEnumerator()
      mkFromEnumerator comparer Empty ie 
    let ofArray comparer l = Array.fold (fun acc k -> add comparer k acc) Empty l    

    // cannot be compared because 'ord contains the comparer which is obtained by SRTP
    [<CustomEquality; NoComparison; StructuredFormatDisplay("{AsString}")>]
    type FunctorizedSet<'a, 'ord when 'a: equality> = FunctorizedSet of Tree<'a> with
      static member inline Wrap x = FunctorizedSet x
      static member inline Unwrap (FunctorizedSet x) = x
      static member Equality (a: FunctorizedSet<_, 'ord>, b: FunctorizedSet<_, 'ord>) =
        use e1 = (toSeq <| unwrap a).GetEnumerator() 
        use e2 = (toSeq <| unwrap b).GetEnumerator() 
        let rec loop () = 
          let m1 = e1.MoveNext() 
          let m2 = e2.MoveNext()
          (m1 = m2) && (not m1 || ((e1.Current = e2.Current) && loop()))
        loop()
      member inline this.ChangeComparerTo<'ord2>() : FunctorizedSet<'a, 'ord2> =
        unwrap this |> wrap
      member this.ComputeHashCode() = 
        let inline combineHash x y = (x <<< 1) + y + 631 
        let mutable res = 0
        for x in this do
          res <- combineHash res (hash x)
        abs res
      override this.GetHashCode() = this.ComputeHashCode()
      override this.Equals(that) = 
        match that with 
          | :? FunctorizedSet<'a, 'ord> as that -> 
            use e1 = (toSeq <| unwrap this).GetEnumerator() 
            use e2 = (toSeq <| unwrap that).GetEnumerator() 
            let rec loop () = 
              let m1 = e1.MoveNext() 
              let m2 = e2.MoveNext()
              (m1 = m2) && (not m1 || ((e1.Current = e2.Current) && loop()))
            loop()
          | _ -> false
      override x.ToString() =
        let tyName =
          sprintf "fset<%s>" (typeof<'ord>.ToString())
        match List.ofSeq (Seq.truncate 4 x) with 
          | [] -> sprintf "%s []" tyName
          | [h1] -> System.Text.StringBuilder().Append(tyName).Append(" [").Append(sprintf "%A" h1).Append("]").ToString()
          | [h1;h2] -> System.Text.StringBuilder().Append(tyName).Append(" [").Append(sprintf "%A" h1).Append("; ").Append(sprintf "%A" h2).Append("]").ToString()
          | [h1;h2;h3] -> System.Text.StringBuilder().Append(tyName).Append(" [").Append(sprintf "%A" h1).Append("; ").Append(sprintf "%A" h2).Append("; ").Append(sprintf "%A" h3).Append("]").ToString()
          | h1 :: h2 :: h3 :: _ -> System.Text.StringBuilder().Append(tyName).Append(" [").Append(sprintf "%A" h1).Append("; ").Append(sprintf "%A" h2).Append("; ").Append(sprintf "%A" h3).Append("; ... ]").ToString() 
      member this.AsString = this.ToString()
      interface IEnumerable<'a> with
        member this.GetEnumerator() = (unwrap this :> IEnumerable<_>).GetEnumerator()
      interface System.Collections.IEnumerable with
        member this.GetEnumerator() = (unwrap this :> System.Collections.IEnumerable).GetEnumerator()
      
namespace FSharp.Collections.Functorized
  open FSharp.Collections.Functorized
  open FSharp.Collections.Functorized.Internal
  open Tree
  open TreeImpl
  open SetImpl

  type FunctorizedSet<'a, 'ord when 'a: equality> = SetImpl.FunctorizedSet<'a, 'ord>
  type fset<'a, 'ord when 'a: equality> = FunctorizedSet<'a, 'ord>

  module Set =
    type Make<'ord> =
      static member inline changeComparerFrom (x: fset<_, 'ord2>) : fset<_, 'ord> = unwrap x |> wrap
      static member inline isEmpty (set: fset<_, 'ord>) = isEmpty (unwrap set)
      static member inline contains x (set: fset<_, ^OrderedType>) =
        let inline comp x y = Comparer.compareBy typrm< ^OrderedType > x y
        unwrap set |> mem comp x
      static member inline add x (set: fset<_, ^OrderedType>) : fset<_, ^OrderedType> =
        let inline comp x y = Comparer.compareBy typrm< ^OrderedType > x y
        unwrap set |> add comp x |> wrap
      static member inline singleton x : fset<_, 'ord> = One x |> wrap
      static member inline remove x (set: fset<_, ^OrderedType>) : fset<_, ^OrderedType> =
        let inline comp x y = Comparer.compareBy typrm< ^OrderedType > x y
        unwrap set |> remove comp x |> wrap
      static member inline union (set1: fset<_, ^OrderedType>) (set2: fset<_, ^OrderedType>) : fset<_, ^OrderedType> =
        let inline comp x y = Comparer.compareBy typrm< ^OrderedType > x y
        union comp (unwrap set1) (unwrap set2) |> wrap
      static member inline unionMany (sets: fset<_, ^OrderedType> seq) : fset<_, ^OrderedType> =
        let inline comp x y = Comparer.compareBy typrm< ^OrderedType > x y
        Seq.fold (fun s1 s2 -> union comp s1 (unwrap s2)) empty sets |> wrap
      static member inline intersect (set1: fset<_, ^OrderedType>) (set2: fset<_, ^OrderedType>) : fset<_, ^OrderedType> =
        let inline comp x y = Comparer.compareBy typrm< ^OrderedType > x y
        intersection comp (unwrap set1) (unwrap set2) |> wrap
      static member inline intersectMany (sets: fset<_, ^OrderedType> seq) : fset<_, ^OrderedType> =
        let inline comp x y = Comparer.compareBy typrm< ^OrderedType > x y
        Seq.fold (fun s1 s2 -> intersection comp s1 (unwrap s2)) empty sets |> wrap
      static member inline iter f (set: fset<_, ^OrderedType>) = iter f (unwrap set)
      static member inline empty () : fset<_, 'ord> = wrap Empty
      static member inline forall predicate (set: fset<_, 'ord>) = forall predicate (unwrap set)
      static member inline exists predicate (set: fset<_, 'ord>) = exists predicate (unwrap set)
      static member inline filter predicate (set: fset<_, ^OrderedType>) : fset<_, ^OrderedType> =
        let inline comp x y = Comparer.compareBy typrm< ^OrderedType > x y
        filter comp predicate (unwrap set) |> wrap
      static member inline partition predicate (set: fset<_, ^OrderedType>) : fset<_, ^OrderedType> * fset<_, ^OrderedType> =
        let inline comp x y = Comparer.compareBy typrm< ^OrderedType > x y
        let set1, set2 = partition comp predicate (unwrap set)
        wrap set1, wrap set2
      static member inline fold f x (set: fset<_, 'ord>) = fold f x (unwrap set)
      static member inline foldBack f (set: fset<_, 'ord>) x = foldBack f (unwrap set) x
      static member inline map f (set: fset<_, ^OrderedType>) : fset<_, ^OrderedType> =
        let inline comp x y = Comparer.compareBy typrm< ^OrderedType > x y
        map comp f (unwrap set) |> wrap
      static member inline count (set: fset<_, 'ord>) = count (unwrap set)
      static member inline toList (set: fset<_, 'ord>) = toList (unwrap set)
      static member inline toArray (set: fset<_, 'ord>) = toArray (unwrap set)
      static member inline toSeq (set: fset<_, 'ord>) = toSeq (unwrap set)
      static member inline appendList (xs: _ list) (set: fset<_, ^OrderedType>) : fset<_, ^OrderedType> =
        let inline comp x y = Comparer.compareBy typrm< ^OrderedType > x y
        xs |> List.fold (fun acc x -> add comp x acc) (unwrap set) |> wrap
      static member inline appendArray (xs: _ array) (set: fset<_, ^OrderedType>) : fset<_, ^OrderedType> =
        let inline comp x y = Comparer.compareBy typrm< ^OrderedType > x y
        xs |> Array.fold (fun acc x -> add comp x acc) (unwrap set) |> wrap
      static member inline appendSeq (xs: _ seq) (set: fset<_, ^OrderedType>) : fset<_, ^OrderedType> =
        let inline comp x y = Comparer.compareBy typrm< ^OrderedType > x y
        xs |> Seq.fold (fun acc x -> add comp x acc) (unwrap set) |> wrap
      static member inline difference (set1: fset<_, ^OrderedType>) (set2: fset<_, ^OrderedType>) : fset<_, ^OrderedType> =
        let inline comp x y = Comparer.compareBy typrm< ^OrderedType > x y
        diff comp (unwrap set1) (unwrap set2) |> wrap
      static member inline isSubset (set1: fset<_, ^OrderedType>) (set2: fset<_, ^OrderedType>) : bool =
        let inline comp x y = Comparer.compareBy typrm< ^OrderedType > x y
        subset comp (unwrap set1) (unwrap set2)
      static member inline isSuperset (set1: fset<_, ^OrderedType>) (set2: fset<_, ^OrderedType>) : bool =
        let inline comp x y = Comparer.compareBy typrm< ^OrderedType > x y
        subset comp (unwrap set2) (unwrap set1)
      static member inline isProperSubset (set1: fset<_, ^OrderedType>) (set2: fset<_, ^OrderedType>) : bool =
        let inline comp x y = Comparer.compareBy typrm< ^OrderedType > x y
        psubset comp (unwrap set1) (unwrap set2)
      static member inline isProperSuperset (set1: fset<_, ^OrderedType>) (set2: fset<_, ^OrderedType>) : bool =
        let inline comp x y = Comparer.compareBy typrm< ^OrderedType > x y
        psubset comp (unwrap set2) (unwrap set1)
      static member inline minElement (set: fset<_, 'ord>) : int =
        minimumElement (unwrap set)
      static member inline maxElement (set: fset<_, 'ord>) : int =
        maximumElement (unwrap set)
      // does not work since you cannnot extract comparer from non-SRTP 'ord
      [<System.Obsolete("Use 'empty() |> appendList xs'.", true)>]
      static member inline ofList (xs: 'a list) : fset<'a, 'ord> = failwith "impossible"
      [<System.Obsolete("Use 'empty() |> appendArray xs'.", true)>]
      static member inline ofArray (xs: 'a array) : fset<'a, 'ord> = failwith "impossible"
      [<System.Obsolete("Use 'empty() |> appendSeq xs'.", true)>]
      static member inline ofSeq (xs: 'a seq) : fset<'a, 'ord> = failwith "impossible"
    
  type DefaultSet = Set.Make<Comparer.Default>
