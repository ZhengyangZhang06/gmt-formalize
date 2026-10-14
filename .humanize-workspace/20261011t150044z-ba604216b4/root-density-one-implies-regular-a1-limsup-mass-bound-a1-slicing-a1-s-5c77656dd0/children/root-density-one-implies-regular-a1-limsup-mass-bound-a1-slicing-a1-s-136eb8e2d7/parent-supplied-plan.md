# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1.gradient_bound_ae-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-136eb8e2d7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1`
- Child key: `gradient_bound_ae`
- Declaration: `Submission.dor_lmbsf_cp_gradient_bound_ae`
- Exact Lean type: `(∀ (d : ℕ) (Z : Set (Euclid d)) (y : Euclid d), Tendsto (fun r => volume (Z ∩ closedBall y r) / volume (closedBall y r)) (𝓝[>] 0) (𝓝 1) → ∀ v : Euclid d, ‖v‖ = 1 → ∃ ys : ℕ → Euclid d, (∀ i, ys i ∈ Z ∧ ys i ≠ y) ∧ Tendsto ys atTop (𝓝 y) ∧ Tendsto (fun i => ‖ys i - y‖⁻¹ • (ys i - y)) atTop (𝓝 v)) → ∀ (m P : ℕ) (Z : Set (Euclid m)) (F : Euclid m → ℝ) (ψ : Euclid m → Euclid P) (f : Euclid P → ℝ) (L : NNReal), MeasurableSet Z → (∀ y ∈ Z, DifferentiableAt ℝ F y ∧ DifferentiableAt ℝ ψ y) → (∀ y ∈ Z, f (ψ y) = F y) → LipschitzWith L f → ∀ᵐ y ∂volume, y ∈ Z → ∀ e : Euclid m, |fderiv ℝ F y e| ≤ (L : ℝ) * ‖fderiv ℝ ψ y e‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
