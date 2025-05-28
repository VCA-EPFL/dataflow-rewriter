# Notes

## Noc language

- First Fix TorusAbsoluteCorrect

- Maybe `netsz` should also be a parameter of the `Noc` structure instead of a
  field

- The `Route` function is currently necessarily deterministic

- There is some hope that we can have definition such as `Route_correct` inside
  the Noc definition which would allow us to guarantee that Noc are correct by
  constructions
  This definition will become much harder if we allow NoC to modify `FlitHeader`

- We need to make a verified compilation to hardware, we could do it by
  compiling to `ExprLow` / `ExprHigh`

- Make a bounded spec

- Make a boundde Router

- Router.init_state should be a relation

## Routers

- Make non homogeneous router

- We don't have access to the rewriting framework, but we could make some sort
  of rewriting by having us say that, when we allow having different spec for a
  router in our spec, if a router implements another, than we preserve
  implementation of spec in the noc
