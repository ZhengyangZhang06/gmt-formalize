# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.tilt_pointwise-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-54c6668573/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1`
- Child key: `tilt_pointwise`
- Declaration: `Submission.idtp_cse_bml_tilt_pointwise_bound`
- Exact Lean type: `∀ (P : ℕ) (R : IMRep (univ : Set (Euclid P)) 2) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (β : Covector (Euclid P) 2), Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → (∀ v : Fin 2 → Euclid P, β v = inner ℝ a (v 0) * inner ℝ e (v 1) - inner ℝ a (v 1) * inner ℝ e (v 0)) → (∀ᵐ x ∂R.measure, (approxTangentPlane 2 R.carrier x).starProjection x = x) → (∀ x : Euclid P, 0 < inner ℝ x a → ‖(approxTangentPlane 2 R.carrier x).starProjection (inner ℝ x a • e - inner ℝ x e • a)‖ ^ 2 / ‖Q.starProjection x‖ ^ 2 ≤ 1) ∧ ∀ᵐ x ∂R.measure, |R.orient x β| ≤ 1 ∧ (0 < inner ℝ x a → 1 - 2 * (1 - |R.orient x β|) ≤ ‖(approxTangentPlane 2 R.carrier x).starProjection (inner ℝ x a • e - inner ℝ x e • a)‖ ^ 2 / ‖Q.starProjection x‖ ^ 2)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
