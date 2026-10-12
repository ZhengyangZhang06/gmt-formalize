# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.chart_data-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-chart-data-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1`
- Child key: `chart_data`
- Declaration: `Submission.slicing_im_st_chart_data`
- Exact Lean type: `∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)) (f : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P), IsOpen U → IsRectifiableTriple U (m + 1) M θ ξ → LipschitzWith L f → (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt (m + 1) M θ x Q → G x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => f (x + s • u)) (inner ℝ (G x) u) 0) → ∃ (Φ : ℕ → Eucl (m + 1) → Eucl P) (Ω A : ℕ → Set (Eucl (m + 1))) (h : ℕ → Eucl (m + 1) → ℝ), (∀ j, IsOpen (Ω j)) ∧ (∀ j, ContDiff ℝ 1 (Φ j)) ∧ (∀ j, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω j, ∀ w' ∈ Ω j, c * ‖w - w'‖ ≤ ‖Φ j w - Φ j w'‖) ∧ (∀ j, A j ⊆ Ω j) ∧ (∀ j, ContDiff ℝ 1 (h j)) ∧ (∀ j, ∀ w ∈ A j, f (Φ j w) = h j w) ∧ (μHE[m + 1] : Measure (Eucl P)) (M \ ⋃ j, Φ j '' A j) = 0 ∧ ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∀ j, ∀ w ∈ A j, Φ j w = x → HasWeightedApproximateTangentSpaceAt (m + 1) M θ x (LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap) ∧ G x ∈ LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap ∧ ∀ u : Eucl (m + 1), inner ℝ (G x) (fderiv ℝ (Φ j) w u) = fderiv ℝ (h j) w u`

## Sibling prerequisites

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.weighted_tangent_chart-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
