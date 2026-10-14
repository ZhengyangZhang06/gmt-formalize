# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1.local_graph-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-5e2e069e1a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1`
- Child key: `local_graph`
- Declaration: `Submission.slicing_im_st_lsc_local_graph`
- Exact Lean type: `∀ (m : ℕ) (h : Eucl (m + 1) → ℝ) (U : Set (Eucl (m + 1))) (w₀ : Eucl (m + 1)), ContDiff ℝ 1 h → IsOpen U → w₀ ∈ U → fderiv ℝ h w₀ ≠ 0 → ∃ (ψ : Eucl m → Eucl (m + 1)) (r : ℝ) (W : Set (Eucl (m + 1))), ContDiff ℝ 1 ψ ∧ 0 < r ∧ IsOpen W ∧ w₀ ∈ W ∧ (∀ v v' : Eucl m, ‖v - v'‖ ≤ ‖ψ v - ψ v'‖) ∧ (∀ v ∈ ball (0 : Eucl m) r, ψ v ∈ U ∧ h (ψ v) = h w₀ ∧ fderiv ℝ h (ψ v) ≠ 0) ∧ ∀ w ∈ W, h w = h w₀ → ∃ v ∈ ball (0 : Eucl m) r, ψ v = w`

## Sibling prerequisites

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1.kernel_frame-a1`
- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1.c1_extension-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
