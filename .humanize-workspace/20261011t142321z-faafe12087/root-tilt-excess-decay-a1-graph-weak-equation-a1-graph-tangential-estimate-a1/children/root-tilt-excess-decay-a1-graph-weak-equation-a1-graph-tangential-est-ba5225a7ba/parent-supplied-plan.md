# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tangential_estimate-a1.graph_image_geometry-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-graph-tangential-est-ba5225a7ba/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tangential_estimate-a1`
- Child key: `graph_image_geometry`
- Declaration: `Submission.gte_graph_image_geometry`
- Exact Lean type: `∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), Continuous (fun p : Rn n × Rn ℓ => graphPoint p.1 p.2) ∧ Continuous (fun z : Amb n ℓ => (EuclideanSpace.finAddEquivProd (q.symm z)).1) ∧ (∀ (x : Rn n) (y : Rn ℓ), (EuclideanSpace.finAddEquivProd (q.symm (q (graphPoint x y)))).1 = x) ∧ ∀ (f : Rn n → Rn ℓ) (R r : ℝ), ContinuousOn f (closedBall 0 R) → r ≤ R → IsCompact (q '' graphOver f (closedBall 0 R)) ∧ MeasurableSet (q '' graphOver f (ball 0 r))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
