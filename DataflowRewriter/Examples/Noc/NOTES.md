# Notes

## Noc language

- Maybe `netsz` should also be a parameter of the `Noc` structure instead of a
  field

- There is some hope that we can have definitions such as `Route_correct` inside
  the Noc definition which would allow us to guarantee that Noc are correct by
  constructions
  This definition will become much harder if we allow NoC to modify `FlitHeader`

- We should have a `List.foldlFinIdx`

- For `BuildExpr`, we need a function `neigh_conn` or something which returns an
  assocList of connections, we could prove this function correct separately and
  it would be a lot easier to use

- `UnboundedQueueInUnboundedBag` could be proven using `RouterIn`

- We want to simplify as much as possible the `BuildExpr` function.
  Avoiding having to rely on complex `bijectivePortRenaming` and custom
  `stringify` functions could be of great help

## Routing Policy

- The `Route` function is currently necessarily deterministic, which we don't
  want

## Routers

- `Router.init_state` should be a relation

- Non homogeneous router
