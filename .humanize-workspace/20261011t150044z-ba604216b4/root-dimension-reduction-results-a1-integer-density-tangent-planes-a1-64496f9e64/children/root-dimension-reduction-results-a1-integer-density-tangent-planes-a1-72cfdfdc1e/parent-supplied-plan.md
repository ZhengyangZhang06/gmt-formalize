# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.sector_points-a1.sector_open-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-72cfdfdc1e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.sector_points-a1`
- Child key: `sector_open`
- Declaration: `Submission.idtp_cse_sp_sector_rel_open`
- Exact Lean type: `∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (δ t φ : ℝ), Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → δ ≤ Real.pi → 0 < t → 0 < φ → φ < δ → ∃ r : ℝ, 0 < r ∧ ∀ y : Euclid P, y ∈ Q → dist y (t • (Real.cos φ • a + Real.sin φ • e)) < r → ∃ t' φ' : ℝ, 0 < t' ∧ 0 < φ' ∧ φ' < δ ∧ y = t' • (Real.cos φ' • a + Real.sin φ' • e)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
