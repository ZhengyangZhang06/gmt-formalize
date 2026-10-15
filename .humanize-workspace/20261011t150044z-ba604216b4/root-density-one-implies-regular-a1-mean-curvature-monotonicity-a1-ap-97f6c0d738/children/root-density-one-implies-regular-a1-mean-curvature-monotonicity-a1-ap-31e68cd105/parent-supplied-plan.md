# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.approx_tangent_in_tangent_space-a1.secant_range-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ap-31e68cd105/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.approx_tangent_in_tangent_space-a1`
- Child key: `secant_range`
- Declaration: `Submission.dsmc_att_mem_range_of_secant_blowUp`
- Exact Lean type: `∀ (P d : ℕ) (N : Set (Euclid P)) (x w : Euclid P) (A : Euclid d →L[ℝ] Euclid P), (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ N, dist y x < δ → ∃ a : Euclid d, ‖y - x - A a‖ ≤ ε * ‖y - x‖) → (∀ s : ℝ, 0 < s → ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ y ∈ N, ‖lam⁻¹ • (y - x) - w‖ < s) → w ∈ Set.range A`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
