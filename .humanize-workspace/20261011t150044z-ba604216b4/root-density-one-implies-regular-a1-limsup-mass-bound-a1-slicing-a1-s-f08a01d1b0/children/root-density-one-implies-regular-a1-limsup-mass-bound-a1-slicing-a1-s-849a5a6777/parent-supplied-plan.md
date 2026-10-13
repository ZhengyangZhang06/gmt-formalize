# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_slice_tangent-a1.level_set_chart_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-849a5a6777/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_slice_tangent-a1`
- Child key: `level_set_chart_cover`
- Declaration: `Submission.dor_lmbsf_pst_level_set_chart_cover`
- Exact Lean type: `∀ (n : ℕ) (W : Set (Euclid (n + 1))) (F : Euclid (n + 1) → ℝ) (t : ℝ), IsOpen W → ContDiff ℝ 1 F → ∃ (D : ℕ → Set (Euclid n)) (Λ : ℕ → Euclid n → Euclid (n + 1)) (c : ℕ → Euclid n) (ρ : ℕ → ℝ), (∀ k, IsOpen (D k)) ∧ (∀ k, ContDiffOn ℝ 1 (Λ k) (D k)) ∧ (∀ k, InjOn (Λ k) (D k)) ∧ (∀ k, ∀ z ∈ D k, Λ k z ∈ W ∧ F (Λ k z) = t ∧ Injective (fderiv ℝ (Λ k) z) ∧ LinearMap.range (fderiv ℝ (Λ k) z : Euclid n →ₗ[ℝ] Euclid (n + 1)) = LinearMap.ker (fderiv ℝ F (Λ k z) : Euclid (n + 1) →ₗ[ℝ] ℝ)) ∧ (∀ k, closedBall (c k) (ρ k) ⊆ D k) ∧ ∀ y ∈ W, fderiv ℝ F y ≠ 0 → F y = t → ∃ k, ∃ z ∈ ball (c k) (ρ k), Λ k z = y`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_slice_tangent-a1.level_set_local_chart-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
