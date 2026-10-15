# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.box-a1.slice_area-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-8f6f377b03/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.box-a1`
- Child key: `slice_area`
- Declaration: `Submission.slicing_im_creg_box_slice_area`
- Exact Lean type: `∀ (P m : ℕ) (Φ : Eucl (m + 1) → Eucl P) (Ω : Set (Eucl (m + 1))) (B : Set (Eucl (m + 1))) (χ : Eucl (m + 1) → Eucl (m + 1)) (S : Set (Eucl (m + 1))) (g : Eucl P → ℝ≥0∞), ContDiff ℝ 1 Φ → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → IsOpen B → ContDiffOn ℝ 1 χ B → χ '' B ⊆ Ω → (∃ Λ : ℝ≥0, LipschitzOnWith Λ χ B) → (∀ (t : ℝ) (v v' : Eucl m), (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v)) ∈ B → (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v')) ∈ B → ‖v - v'‖ ≤ ‖χ ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v))) - χ ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v')))‖) → MeasurableSet S → Measurable g → ∀ t : ℝ, ∫⁻ x in (fun v : Eucl m => Φ (χ ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v))))) '' {v : Eucl m | (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v)) ∈ B ∩ χ ⁻¹' S}, g x ∂(μHE[m] : Measure (Eucl P)) = ∫⁻ v : Eucl m, (B ∩ χ ⁻¹' S).indicator (fun y => g (Φ (χ y)) * ENNReal.ofReal (Real.sqrt (Matrix.of fun i j : Fin m => inner ℝ (fderiv ℝ Φ (χ y) (fderiv ℝ χ y (EuclideanSpace.single i.succ 1))) (fderiv ℝ Φ (χ y) (fderiv ℝ χ y (EuclideanSpace.single j.succ 1)))).det)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v))) ∂(volume : Measure (Eucl m))`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.chart_change_of_variables-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
