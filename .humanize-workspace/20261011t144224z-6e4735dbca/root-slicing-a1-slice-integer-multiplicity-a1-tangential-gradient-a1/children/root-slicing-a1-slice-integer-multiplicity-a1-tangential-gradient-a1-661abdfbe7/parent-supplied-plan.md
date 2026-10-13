# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_gradient-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-661abdfbe7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1`
- Child key: `chart_gradient`
- Declaration: `Submission.slicing_im_tg_chart_gradient`
- Exact Lean type: `∀ (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (f : Eucl P → ℝ) (L : ℝ≥0), IsOpen Ω → ContDiff ℝ 1 Φ → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → LipschitzWith L f → ∃ g : Eucl P → Eucl P, Measurable g ∧ (∀ x, ‖g x‖ ≤ L) ∧ ∀ᵐ y ∂((μHE[n] : Measure (Eucl P)).restrict (Φ '' Ω)), ∀ w ∈ Ω, Φ w = y → g y ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap ∧ ∀ v ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap, HasDerivAt (fun s : ℝ => f (y + s • v)) (inner ℝ (g y) v) 0`

## Sibling prerequisites

- `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.line_deriv-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
