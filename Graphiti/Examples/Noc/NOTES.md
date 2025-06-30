# Notes

## Noc language

- `UnboundedQueueInUnboundedBag` could be proven using `RouterIn`

## Routing Policy

- The `Route` function is currently necessarily deterministic, which we don't
  want

## Routers

- `Router.init_state` should be a relation

- Non homogeneous routers: They are a huge pain and should be left for later

## Interesting for later

- Study how deadlock freedom is a liveness property in trace-based semantics:
  + Study how to express liveness property refinement. A thing would be to have
    a φ which is preserved with a ∀ instead of an ∃

## Other

- We want an implementation of an ordered router and show that it is correct, so
  that we can use it to implement a `Torus` router and we can actually extract
  it to hardware

- Tried using Vector for `fin_range` to keep the length information in the type
  to avoid cast, did not work

- We need to clean up proofs and definitions, it is getting everywhere…

- We need to simplify `dep_foldr` when β is a product type, so when we are
  producing DPList'
