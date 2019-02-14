FSharp.Collections.Functorized
==============================

Functorized collections for F#!

The FSharp.CommandLine library can be [installed from NuGet](https://www.nuget.org/packages/FSharp.Collections.Functorized):

```
PM> Install-Package FSharp.Collections.Functorized
```

## Example

```fsharp
open System
open FSharp.Collections.Functorized

type IgnoreCaseStrComparer() =
  static let cmp = StringComparer.OrdinalIgnoreCase
  static member inline Compare (s1, s2) = cmp.Compare(s1, s2)

type LengthComparer() =
  static member inline Compare (s1: string, s2: string) = compare s1.Length s2.Length

type IgnoreCaseSet = Set.Make<IgnoreCaseStrComparer>
type LengthSet = Set.Make<LengthComparer>

let icset =
  IgnoreCaseSet.empty()
  |> IgnoreCaseSet.add "foo"

let lenset =
  LengthSet.empty()
  |> LengthSet.add "foo"

icset |> IgnoreCaseSet.contains "Foo" |> printfn "%b" // true
lenset |> IgnoreCaseSet.contains "bar" |> printfn "%b" // true
```