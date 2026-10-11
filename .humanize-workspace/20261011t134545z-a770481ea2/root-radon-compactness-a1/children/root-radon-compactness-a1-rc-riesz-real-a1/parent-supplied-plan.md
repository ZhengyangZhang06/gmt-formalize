# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.radon_compactness-a1.rc_riesz_real-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/nodes/root-radon-compactness-a1-rc-riesz-real-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.radon_compactness-a1`
- Child key: `rc_riesz_real`
- Declaration: `Submission.rc_riesz_real`
- Exact Lean type: `RieszPositive.{u} → ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ), (∀ f : C_c(X, ℝ), 0 ≤ f → 0 ≤ Λ f) → ∃ μ : OuterMeasure X, IsRadonOuterMeasure μ ∧ ∀ f : C_c(X, ℝ), Λ f = ∫ x, f x ∂caratheodoryMeasure μ`

## Sibling prerequisites

- `root.radon_compactness-a1.rc_cc_integrable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
