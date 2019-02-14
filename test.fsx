#r "src/bin/Release/net46/FSharp.Collections.Functorized.dll"
open FSharp.Collections.Functorized;;

type StrComparer =
  static member inline Compare (s, t) = System.StringComparer.Ordinal.Compare(s, t);;

type StrComparer2() =
  static let cmp = System.StringComparer.Ordinal
  static member inline Compare (s, t) = cmp.Compare(s, t);;

type Set2 = Set.Make<StrComparer>;;
type Set3 = Set.Make<StrComparer2>;;
type Set4 = Set.Make<Comparer.Default>;;

let randStr() = System.IO.Path.GetRandomFileName();;

let data = [| for i = 1 to 10000 do yield randStr() |];;

let set1 = Set.ofArray data;;
let set2 = Set2.empty() |> Set2.appendArray data;;
let set3 = Set3.empty() |> Set3.appendArray data;;
let set4 = Set4.empty() |> Set4.appendArray data;;

#time "on";;

for i = 1 to 100 do ignore <| Set.ofArray data;;
for i = 1 to 100 do Set2.empty() |> Set2.appendArray data |> ignore;;
for i = 1 to 100 do Set3.empty() |> Set3.appendArray data |> ignore;;
for i = 1 to 100 do Set4.empty() |> Set4.appendArray data |> ignore;;

for i = 1 to 100000 do set1 |> Set.contains (randStr()) |> ignore;;
for i = 1 to 100000 do set2 |> Set2.contains (randStr()) |> ignore;;
for i = 1 to 100000 do set3 |> Set3.contains (randStr()) |> ignore;;
for i = 1 to 100000 do set4 |> Set4.contains (randStr()) |> ignore;;

