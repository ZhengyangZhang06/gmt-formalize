# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.affine_approximation-a1.height_bound_small_delta-a1.packing_finite_net-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-height-bound-small-delta-a1-packing-finite-net-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.affine_approximation-a1.height_bound_small_delta-a1`
- Child key: `packing_finite_net`
- Declaration: `Submission.aal_packing_finite_net`
- Exact Lean type: `∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) (S E : Set X) (r a b : ℝ), 0 < r → 0 < a → 0 ≤ b → μ E ≤ ENNReal.ofReal b → (∀ y ∈ S, closedBall y r ⊆ E ∧ ENNReal.ofReal a ≤ μ (closedBall y r)) → ∃ F : Finset X, (↑F : Set X) ⊆ S ∧ (F.card : ℝ) * a ≤ b ∧ ∀ y ∈ S, ∃ z ∈ F, dist y z ≤ 2 * r`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
