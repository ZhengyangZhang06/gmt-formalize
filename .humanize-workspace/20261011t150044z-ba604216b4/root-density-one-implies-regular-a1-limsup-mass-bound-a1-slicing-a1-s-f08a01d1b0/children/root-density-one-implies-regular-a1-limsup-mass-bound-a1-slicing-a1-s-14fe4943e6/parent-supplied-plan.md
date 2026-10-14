# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_slice_tangent-a1.level_set_local_chart-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-14fe4943e6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_slice_tangent-a1`
- Child key: `level_set_local_chart`
- Declaration: `Submission.dor_lmbsf_pst_level_set_local_chart`
- Exact Lean type: `∀ (n : ℕ) (W : Set (Euclid (n + 1))) (F : Euclid (n + 1) → ℝ) (y₀ : Euclid (n + 1)), IsOpen W → ContDiff ℝ 1 F → y₀ ∈ W → fderiv ℝ F y₀ ≠ 0 → ∃ (D : Set (Euclid n)) (Λ : Euclid n → Euclid (n + 1)) (c : Euclid n) (ρ : ℝ) (N : Set (Euclid (n + 1))), IsOpen D ∧ ContDiffOn ℝ 1 Λ D ∧ InjOn Λ D ∧ (∀ z ∈ D, Λ z ∈ W ∧ F (Λ z) = F y₀ ∧ Injective (fderiv ℝ Λ z) ∧ LinearMap.range (fderiv ℝ Λ z : Euclid n →ₗ[ℝ] Euclid (n + 1)) = LinearMap.ker (fderiv ℝ F (Λ z) : Euclid (n + 1) →ₗ[ℝ] ℝ)) ∧ closedBall c ρ ⊆ D ∧ IsOpen N ∧ y₀ ∈ N ∧ N ∩ F ⁻¹' {F y₀} ⊆ Λ '' ball c ρ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
