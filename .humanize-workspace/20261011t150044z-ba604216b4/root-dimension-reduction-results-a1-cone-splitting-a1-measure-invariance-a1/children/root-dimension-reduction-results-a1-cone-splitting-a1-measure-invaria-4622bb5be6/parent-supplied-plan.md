# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.measure_invariance-a1.dilate_homogeneity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-measure-invaria-4622bb5be6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.measure_invariance-a1`
- Child key: `dilate_homogeneity`
- Declaration: `Submission.dimred_cs_mi_withDensity_dilate`
- Exact Lean type: `∀ (P n : ℕ) (f : Euclid P → ℝ≥0∞) (lam : ℝ), 0 < lam → (∀ x : Euclid P, f (lam • x) = f x) → ∀ A : Set (Euclid P), MeasurableSet A → (μHE[n] : Measure (Euclid P)).withDensity f ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * (μHE[n] : Measure (Euclid P)).withDensity f A`

## Sibling prerequisites

- `root.half_space_cone_lies_in_boundary-a1.cone_measure_homogeneous-a1.dilation_change_of_variables-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
