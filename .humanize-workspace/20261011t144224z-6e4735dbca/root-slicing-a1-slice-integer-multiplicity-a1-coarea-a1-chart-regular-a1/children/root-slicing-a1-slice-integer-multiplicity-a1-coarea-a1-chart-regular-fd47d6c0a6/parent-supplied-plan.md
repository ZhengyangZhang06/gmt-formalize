# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.jacobian-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-fd47d6c0a6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1`
- Child key: `jacobian`
- Declaration: `Submission.slicing_im_creg_jacobian_identity`
- Exact Lean type: `∀ (P m : ℕ) (A : Eucl (m + 1) →L[ℝ] Eucl P) (D : Eucl (m + 1) →L[ℝ] Eucl (m + 1)) (γ : Eucl P), γ ∈ LinearMap.range A.toLinearMap → (∀ y : Eucl (m + 1), inner ℝ γ (A (D y)) = y 0) → Real.sqrt (Matrix.of fun i j : Fin m => inner ℝ (A (D (EuclideanSpace.single i.succ 1))) (A (D (EuclideanSpace.single j.succ 1)))).det = ‖γ‖ * Real.sqrt (Matrix.of fun i j : Fin (m + 1) => inner ℝ (A (EuclideanSpace.single i 1)) (A (EuclideanSpace.single j 1))).det * |D.det|`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
