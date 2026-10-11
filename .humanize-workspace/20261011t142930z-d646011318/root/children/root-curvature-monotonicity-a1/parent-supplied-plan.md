# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.curvature_monotonicity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-curvature-monotonicity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `curvature_monotonicity`
- Declaration: `Submission.mean_curvature_monotonicity`
- Exact Lean type: `(∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ), 0 < n → IsFiniteMeasureOnCompacts V.weight ∧ (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) ∧ AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight) → BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity`

## Sibling prerequisites

- `root.weighted_monotonicity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
