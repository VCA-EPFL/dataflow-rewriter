# Notes

## Noc language

- Maybe `netsz` should also be a parameter of the `Noc` structure instead of a
  field

- There is some hope that we can have definitions such as `Route_correct` inside
  the Noc definition which would allow us to guarantee that Noc are correct by
  constructions
  This definition will become much harder if we allow NoC to modify `FlitHeader`

- We should have a `List.foldlFinIdx`

- `UnboundedQueueInUnboundedBag` could be proven using `RouterIn`

- We want to simplify as much as possible the `BuildExpr` function.
  Avoiding having to rely on complex `bijectivePortRenaming` and custom
  `stringify` functions could be of great help

## Routing Policy

- The `Route` function is currently necessarily deterministic, which we don't
  want

## Routers

- `Router.init_state` should be a relation

- Non homogeneous routers

## BuildExprCorrect

- To show the correctness, we want to simplify as much as possible the
  `BuildExpr` function.
  To this end, it would be nice if we could remove the renaming of router ports,
  because it introduce annoying bijectivePortRenaming.
  To still be able to prove the MatchInterface, we could actually do a
  portRenaming on the noc _module_, and not on the noc _expression module_.

## Interesting for later

- Study how deadlock freedom is a liveness property in trace-based semantics:
  + Study how to express liveness property refinement. A thing would be to have
    a φ which is preserved with a ∀ instead of an ∃
