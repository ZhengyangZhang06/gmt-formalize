# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-aee3915817/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1`
- Child key: `level_set_charts`
- Declaration: `Submission.slicing_im_st_level_set_charts`
- Exact Lean type: `∀ (P m : ℕ) (Φ : Eucl (m + 1) → Eucl P) (Ω : Set (Eucl (m + 1))) (h : Eucl (m + 1) → ℝ) (t : ℝ), IsOpen Ω → ContDiff ℝ 1 Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ContDiff ℝ 1 h → ∃ (Ψ : ℕ → Eucl m → Eucl P) (V : ℕ → Set (Eucl m)), (∀ i, IsOpen (V i)) ∧ (∀ i, ContDiff ℝ 1 (Ψ i)) ∧ (∀ i, ∃ K : ℝ≥0, LipschitzOnWith K (Ψ i) (V i)) ∧ (∀ i, ∃ c : ℝ, 0 < c ∧ ∀ v ∈ V i, ∀ v' ∈ V i, c * ‖v - v'‖ ≤ ‖Ψ i v - Ψ i v'‖) ∧ (∀ w ∈ Ω, h w = t → fderiv ℝ h w ≠ 0 → ∃ i, ∃ v ∈ V i, Ψ i v = Φ w) ∧ ∀ i, ∀ v ∈ V i, ∃ w ∈ Ω, h w = t ∧ Ψ i v = Φ w ∧ LinearMap.range (fderiv ℝ (Ψ i) v).toLinearMap = Submodule.map (fderiv ℝ Φ w).toLinearMap (LinearMap.ker (fderiv ℝ h w).toLinearMap)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
