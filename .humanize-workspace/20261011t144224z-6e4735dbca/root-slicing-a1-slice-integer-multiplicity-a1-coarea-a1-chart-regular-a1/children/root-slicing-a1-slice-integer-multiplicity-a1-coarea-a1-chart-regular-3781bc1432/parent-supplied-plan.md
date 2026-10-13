# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.straighten-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-3781bc1432/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1`
- Child key: `straighten`
- Declaration: `Submission.slicing_im_creg_straightening`
- Exact Lean type: `∀ (m : ℕ) (h : Eucl (m + 1) → ℝ) (Ω : Set (Eucl (m + 1))) (w₀ : Eucl (m + 1)), IsOpen Ω → w₀ ∈ Ω → ContDiff ℝ 1 h → fderiv ℝ h w₀ ≠ 0 → ∃ (B : Set (Eucl (m + 1))) (χ : Eucl (m + 1) → Eucl (m + 1)), IsOpen B ∧ ContDiffOn ℝ 1 χ B ∧ IsOpen (χ '' B) ∧ w₀ ∈ χ '' B ∧ χ '' B ⊆ Ω ∧ (∃ Λ : ℝ≥0, LipschitzOnWith Λ χ B) ∧ (∀ y ∈ B, h (χ y) = y 0) ∧ ∀ (t : ℝ) (v v' : Eucl m), (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v)) ∈ B → (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v')) ∈ B → ‖v - v'‖ ≤ ‖χ ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v))) - χ ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v')))‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
