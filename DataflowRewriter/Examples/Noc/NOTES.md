# Notes

## Noc language

- We would like to have Routers be a parameter of the Noc definition, so that we
  can have routers with bounded state, which behaves more like a bag, ....
  They can still be homogeneous in a first place, since this probably cover most
  use cases, but in the final form it would be better for them to be
  heterogeneous.
  This requires changing `Noc.input_rel` and `Noc.output_rel`

- The Route function should depend on `cur` and on `FlitHeader`, not on `cur`
  and `dst`

- The definition of `FlitHeader` should be Noc-dependent

- Maybe the routing function could actually also modify the `FlitHeader`.
  This would model some stateful behavior

- The interface of a Router we want is probably more to have a `Data × dst` on
  input and a `Data` on output.
  This would make the interface match no mater the definition of a `FlitHeader`.
  This requires having a function which creates a `FlitHeader` from a
  `Data × dst`.

- `Data` should maybe be a parameter of the `Noc` structure instead of a field

- The `Route` function is currently necessarily deterministic

- We don't have access to the rewriting framework, but we could make some sort
  of rewriting by having us say that, when we allow having different spec for a
  router in our spec, if a router implements another, than we preserve
  implementation of spec in the noc

- There is some hope that we can have definition such as `Route_correct` inside
  the Noc definition which would allow us to guarantee that Noc are correct by
  constructions
  This definition will become much harder if we allow NoC to modify `FlitHeader`

- We need to make a verified compilation to hardware, we could do it by
  compiling to `ExprLow` / `ExprHigh`

- Make a bounded spec. Boundedness may be very hard to describe properly as
  there may be inter-dependencies between channels which are hard to describe?
  A channel being blocked may block other channels
