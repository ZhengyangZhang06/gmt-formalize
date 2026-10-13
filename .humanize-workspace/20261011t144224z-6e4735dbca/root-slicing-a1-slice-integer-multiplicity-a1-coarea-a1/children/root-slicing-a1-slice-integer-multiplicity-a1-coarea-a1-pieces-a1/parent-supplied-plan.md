# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.pieces-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-pieces-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1`
- Child key: `pieces`
- Declaration: `Submission.slicing_im_coarea_pieces`
- Exact Lean type: `∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)) (f : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P), IsOpen U → IsRectifiableTriple U (m + 1) M θ ξ → LipschitzWith L f → (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt (m + 1) M θ x Q → G x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => f (x + s • u)) (inner ℝ (G x) u) 0) → ∃ (Φ : ℕ → Eucl (m + 1) → Eucl P) (Ω : ℕ → Set (Eucl (m + 1))) (h : ℕ → Eucl (m + 1) → ℝ) (W : ℕ → Set (Eucl P)), (∀ i, IsOpen (Ω i)) ∧ (∀ i, ContDiff ℝ 1 (Φ i)) ∧ (∀ i, ∃ K : ℝ≥0, LipschitzOnWith K (Φ i) (Ω i)) ∧ (∀ i, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω i, ∀ w' ∈ Ω i, c * ‖w - w'‖ ≤ ‖Φ i w - Φ i w'‖) ∧ (∀ i, ContDiff ℝ 1 (h i)) ∧ (∀ i, MeasurableSet (W i)) ∧ (∀ i, W i ⊆ M) ∧ (∀ i, W i ⊆ Φ i '' Ω i) ∧ Pairwise (Function.onFun Disjoint W) ∧ (μHE[m + 1] : Measure (Eucl P)) (M \ ⋃ i, W i) = 0 ∧ ∀ i, ∀ w ∈ Ω i, Φ i w ∈ W i → f (Φ i w) = h i w ∧ G (Φ i w) ∈ LinearMap.range (fderiv ℝ (Φ i) w).toLinearMap ∧ ∀ u, inner ℝ (G (Φ i w)) (fderiv ℝ (Φ i) w u) = fderiv ℝ (h i) w u`

## Sibling prerequisites

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.c1_approx-a1`
- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_cover-a1`
- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_tangent-a1`
- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.line_deriv-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
