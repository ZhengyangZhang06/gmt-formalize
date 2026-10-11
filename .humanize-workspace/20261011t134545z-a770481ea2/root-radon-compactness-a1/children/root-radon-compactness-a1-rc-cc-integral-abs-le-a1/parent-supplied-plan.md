# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.radon_compactness-a1.rc_cc_integral_abs_le-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/nodes/root-radon-compactness-a1-rc-cc-integral-abs-le-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.radon_compactness-a1`
- Child key: `rc_cc_integral_abs_le`
- Declaration: `Submission.rc_cc_integral_abs_le`
- Exact Lean type: `∀ (X : Type u) [TopologicalSpace X] (μ : OuterMeasure X), IsRadonOuterMeasure μ → ∀ (f : C_c(X, ℝ)) (C : ℝ), (∀ x, |f x| ≤ C) → |∫ x, f x ∂caratheodoryMeasure μ| ≤ (μ (tsupport f)).toReal * C`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
