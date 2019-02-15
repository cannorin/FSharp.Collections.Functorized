FSharp.Collections.Functorized
==============================

Functorized collections for F#!

The FSharp.Collections.Functorized library can be [installed from NuGet](https://www.nuget.org/packages/FSharp.Collections.Functorized):

```
PM> Install-Package FSharp.Collections.Functorized
```

## Functors

* [`Set.Make< ^OrderedType >`](https://github.com/cannorin/FSharp.Collections.Functorized/blob/master/src/Set.fs#L250)
  * `when ^OrderedType: (static member Compare: 'a * 'a -> int)`
* [`Map.Make< ^OrderedType >`](https://github.com/cannorin/FSharp.Collections.Functorized/blob/master/src/Map.fs#L305)
  * `when ^OrderedType: (static member Compare: 'a * 'a -> int)`

## Built-In Instantiations

* [`DefaultSet`](https://github.com/cannorin/FSharp.Collections.Functorized/blob/master/src/Set.fs#L331)
* [`DefaultMap`](https://github.com/cannorin/FSharp.Collections.Functorized/blob/master/src/Map.fs#L356)
  * Uses the default [`compare: 'T -> 'T -> int when 'T: comparison` ](https://msdn.microsoft.com/en-us/visualfsharpdocs/conceptual/operators.compare%5B%27t%5D-function-%5Bfsharp%5D) operator.

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
lenset |> LengthSet.contains "bar" |> printfn "%b" // true
```