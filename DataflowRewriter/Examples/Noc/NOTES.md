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

## Routing Policy

- The `Route` function is currently necessarily deterministic, which we don't
  want

## Routers

- `Router.init_state` should be a relation

- Non homogeneous routers

## Interesting for later

- Study how deadlock freedom is a liveness property in trace-based semantics:
  + Study how to express liveness property refinement. A thing would be to have
    a φ which is preserved with a ∀ instead of an ∃
