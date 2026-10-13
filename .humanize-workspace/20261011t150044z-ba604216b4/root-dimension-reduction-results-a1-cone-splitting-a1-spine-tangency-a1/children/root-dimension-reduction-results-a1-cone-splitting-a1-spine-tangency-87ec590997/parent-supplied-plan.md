# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.spine_tangency-a1.ball_scaling-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-spine-tangency-87ec590997/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.spine_tangency-a1`
- Child key: `ball_scaling`
- Declaration: `Submission.dimred_cs_st_closedBall_measure_scaling`
- Exact Lean type: `∀ (P n : ℕ) (μ : Measure (Euclid P)) (L : Submodule ℝ (Euclid P)), (∀ y ∈ L, ∀ A : Set (Euclid P), MeasurableSet A → μ ((fun x => y + x) ⁻¹' A) = μ A) → (∀ lam : ℝ, 0 < lam → ∀ A : Set (Euclid P), MeasurableSet A → μ ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * μ A) → ∀ z ∈ L, ∀ ρ : ℝ, 0 < ρ → μ (closedBall z ρ) = ENNReal.ofReal (ρ ^ n) * μ (closedBall z 1)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
