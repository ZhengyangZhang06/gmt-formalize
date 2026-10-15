# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.poincare_sum-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-poincare-sum-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1`
- Child key: `poincare_sum`
- Declaration: `Submission.fiw_tb_tda_poincare_sum`
- Exact Lean type: `∀ m : ℕ, ∃ c : ℝ≥0, ∀ (ρ : ℝ), 0 < ρ → ∀ (u : Eucl (m + 1) → ℝ) (Λ : ℝ≥0∞), Measurable u → (∀ h : Eucl (m + 1), ∫⁻ x, ENNReal.ofReal |u (x + h) - u x| ≤ ENNReal.ofReal ‖h‖ * Λ) → ∑' F : LatticeFaceIndex (m + 1) (m + 1), ENNReal.ofReal (ρ ^ (m + 1))⁻¹ * ∫⁻ x in latticeFace ρ F, ∫⁻ y in latticeFace ρ F, ENNReal.ofReal |u x - u y| ≤ c * ENNReal.ofReal ρ * Λ`

## Sibling prerequisites

- `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.lattice_cubes-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
