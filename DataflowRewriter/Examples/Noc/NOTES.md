# Notes

## Noc language

- Maybe `netsz` should also be a parameter of the `Noc` structure instead of a
  field

- The `Route` function is currently necessarily deterministic, which we don't
  want

- There is some hope that we can have definitions such as `Route_correct` inside
  the Noc definition which would allow us to guarantee that Noc are correct by
  constructions
  This definition will become much harder if we allow NoC to modify `FlitHeader`

- We need to make a verified compilation to hardware, we could do it by
  compiling to `ExprLow`

- Make a bounded spec

- Make a bounded Router

- `Router.init_state` should be a relation

- We should have a `List.foldlFinIdx`

- We have the problem that we don't know to which input we are connecting in the
  topology, but this is an information which could be important...
  It would be very helpful for the neigh function to be some sort of
  Bijection, or we can have two function `neigh_out` and `neigh_inp` and a proof
  that they are sort of bijective

## Routers

- Non homogeneous router

- We don't have direct access to the rewriting framework, but we could make some
  sort of rewriting by having us say that, when we allow having different spec
  for a router in our spec, if a router implements another, than we preserve
  implementation of spec in the noc
