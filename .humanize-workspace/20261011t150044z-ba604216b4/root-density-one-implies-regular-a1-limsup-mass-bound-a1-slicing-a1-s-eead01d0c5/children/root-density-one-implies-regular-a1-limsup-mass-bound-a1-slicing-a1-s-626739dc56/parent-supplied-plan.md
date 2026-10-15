# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1.cutoff_deriv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-626739dc56/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1`
- Child key: `cutoff_deriv`
- Declaration: `Submission.dor_lmbsf_pwl_fderiv_cutoff_comp_ae`
- Exact Lean type: `(∀ (d : ℕ) (Z : Set (Euclid d)) (y : Euclid d), Tendsto (fun r => volume (Z ∩ closedBall y r) / volume (closedBall y r)) (𝓝[>] 0) (𝓝 1) → ∀ v : Euclid d, ‖v‖ = 1 → ∃ ys : ℕ → Euclid d, (∀ i, ys i ∈ Z ∧ ys i ≠ y) ∧ Tendsto ys atTop (𝓝 y) ∧ Tendsto (fun i => ‖ys i - y‖⁻¹ • (ys i - y)) atTop (𝓝 v)) → ∀ (d : ℕ) (Z : Set (Euclid d)) (F u : Euclid d → ℝ) (K : NNReal) (a b : ℝ), MeasurableSet Z → Differentiable ℝ F → LipschitzWith K u → a < b → (∀ y ∈ Z, u y = min 1 (max 0 ((b - F y) / (b - a)))) → ∀ᵐ y ∂(volume : Measure (Euclid d)), y ∈ Z → fderiv ℝ u y = (if a < F y ∧ F y < b then -(b - a)⁻¹ else 0) • fderiv ℝ F y`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1.eqon_deriv-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
