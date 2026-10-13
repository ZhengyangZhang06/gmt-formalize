# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.signed_change_of_variables-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1-sign-b01f3ae29c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1`
- Child key: `signed_change_of_variables`
- Declaration: `Submission.deformation_ipl_cc_signed_change_of_variables`
- Exact Lean type: `∀ (P k : ℕ) (Φ : Eucl k → Eucl P) (Ω : Set (Eucl k)) (A : Set (Eucl P)) (h : Eucl P → ℝ), IsOpen Ω → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → A ⊆ Φ '' Ω → NullMeasurableSet A (μHE[k] : Measure (Eucl P)) → IntegrableOn h A (μHE[k] : Measure (Eucl P)) → IntegrableOn (fun w => h (Φ w) * Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det) (Ω ∩ Φ ⁻¹' A) (volume : Measure (Eucl k)) ∧ ∫ x in A, h x ∂(μHE[k] : Measure (Eucl P)) = ∫ w in Ω ∩ Φ ⁻¹' A, h (Φ w) * Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det ∂(volume : Measure (Eucl k))`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.chart_change_of_variables-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
