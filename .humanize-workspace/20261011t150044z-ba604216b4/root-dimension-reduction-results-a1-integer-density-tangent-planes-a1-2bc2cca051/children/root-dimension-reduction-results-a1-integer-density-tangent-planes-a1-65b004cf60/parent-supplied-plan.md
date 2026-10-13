# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_count-a1.planar_geometry-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-65b004cf60/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_count-a1`
- Child key: `planar_geometry`
- Declaration: `Submission.idtp_cse_fc_planar_fibre_geometry`
- Exact Lean type: `∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P), Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → (∀ (T : Submodule ℝ (Euclid P)) (x : Euclid P), ‖T.starProjection (inner ℝ x a • e - inner ℝ x e • a)‖ ≤ ‖Q.starProjection x‖ ∧ ‖Q.starProjection x‖ ≤ ‖x‖) ∧ ∀ t α : ℝ, 0 < t → |α| < Real.pi / 2 → (0 < inner ℝ (t • (Real.cos α • a + Real.sin α • e)) a ∧ ‖t • (Real.cos α • a + Real.sin α • e)‖ = t ∧ Real.arctan (inner ℝ (t • (Real.cos α • a + Real.sin α • e)) e / inner ℝ (t • (Real.cos α • a + Real.sin α • e)) a) = α ∧ Q.starProjection (t • (Real.cos α • a + Real.sin α • e)) = t • (Real.cos α • a + Real.sin α • e) ∧ ‖Q.starProjection (inner ℝ (t • (Real.cos α • a + Real.sin α • e)) a • e - inner ℝ (t • (Real.cos α • a + Real.sin α • e)) e • a)‖ = t) ∧ ∀ x : Euclid P, 0 < inner ℝ x a → ‖x‖ = t → Real.arctan (inner ℝ x e / inner ℝ x a) = α → x ≠ t • (Real.cos α • a + Real.sin α • e) → ‖Q.starProjection x‖ < t`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
