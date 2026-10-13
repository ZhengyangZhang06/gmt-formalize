# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.chart_integral_eq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-eff117824a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1`
- Child key: `chart_integral_eq`
- Declaration: `Submission.slicing_im_ll_twl_chart_integral_eq`
- Exact Lean type: `∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (A : Set (Eucl P)) (F : Eucl P → E), IsOpen Ω → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ κ : ℝ, 0 < κ ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, κ * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → A ⊆ Φ '' Ω → NullMeasurableSet A (μHE[n] : Measure (Eucl P)) → IntegrableOn F A (μHE[n] : Measure (Eucl P)) → NullMeasurableSet (Ω ∩ Φ ⁻¹' A) (volume : Measure (Eucl n)) ∧ IntegrableOn (fun w => Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det • F (Φ w)) (Ω ∩ Φ ⁻¹' A) (volume : Measure (Eucl n)) ∧ ∫ x in A, F x ∂(μHE[n] : Measure (Eucl P)) = ∫ w in Ω ∩ Φ ⁻¹' A, Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det • F (Φ w) ∂(volume : Measure (Eucl n))`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.chart_change_of_variables-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
