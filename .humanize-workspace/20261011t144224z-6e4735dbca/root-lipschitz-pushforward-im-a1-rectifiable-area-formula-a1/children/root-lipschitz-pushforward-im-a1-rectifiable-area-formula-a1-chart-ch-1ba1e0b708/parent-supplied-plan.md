# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.chart_change_of_variables-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-ch-1ba1e0b708/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1`
- Child key: `chart_change_of_variables`
- Declaration: `Submission.lpf_raf_chart_change_of_variables`
- Exact Lean type: `∀ (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (A : Set (Eucl P)) (g : Eucl P → ℝ≥0∞), IsOpen Ω → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → A ⊆ Φ '' Ω → NullMeasurableSet A (μHE[n] : Measure (Eucl P)) → AEMeasurable g ((μHE[n] : Measure (Eucl P)).restrict A) → NullMeasurableSet (Ω ∩ Φ ⁻¹' A) (volume : Measure (Eucl n)) ∧ AEMeasurable (fun w => g (Φ w)) ((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' A)) ∧ ∫⁻ x in A, g x ∂(μHE[n] : Measure (Eucl P)) = ∫⁻ w in Ω ∩ Φ ⁻¹' A, g (Φ w) * ENNReal.ofReal (Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det) ∂(volume : Measure (Eucl n))`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.local_lipschitz_area-a1`
- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.chart_preimage_null-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
