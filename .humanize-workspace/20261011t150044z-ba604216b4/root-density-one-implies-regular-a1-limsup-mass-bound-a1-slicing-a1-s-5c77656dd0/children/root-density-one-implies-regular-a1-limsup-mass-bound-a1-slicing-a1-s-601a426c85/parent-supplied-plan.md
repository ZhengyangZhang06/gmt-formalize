# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1.chart_tangent_lift-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-601a426c85/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1`
- Child key: `chart_tangent_lift`
- Declaration: `Submission.dor_lmbsf_cp_chart_tangent_lift`
- Exact Lean type: `∀ (m P : ℕ) (V : Set (Euclid m)) (ψ : Euclid m → Euclid P) (F : Euclid m → ℝ), IsOpen V → ContDiffOn ℝ 1 ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ContDiff ℝ 1 F → ∃ Φ : Euclid m → Euclid P, ContinuousOn Φ V ∧ ∀ y ∈ V, Φ y ∈ LinearMap.range (fderiv ℝ ψ y : Euclid m →ₗ[ℝ] Euclid P) ∧ (∀ e : Euclid m, inner ℝ (Φ y) (fderiv ℝ ψ y e) = fderiv ℝ F y e) ∧ ∀ L : NNReal, (∀ e : Euclid m, |fderiv ℝ F y e| ≤ (L : ℝ) * ‖fderiv ℝ ψ y e‖) → ‖Φ y‖ ≤ (L : ℝ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
