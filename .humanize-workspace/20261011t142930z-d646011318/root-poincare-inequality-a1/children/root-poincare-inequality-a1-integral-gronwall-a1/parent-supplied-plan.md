# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.poincare_inequality-a1.integral_gronwall-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-poincare-inequality-a1-integral-gronwall-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.poincare_inequality-a1`
- Child key: `integral_gronwall`
- Declaration: `Submission.backward_integral_gronwall_Ioc`
- Exact Lean type: `∀ (a b Λ C : ℝ) (f : ℝ → ℝ), a ≤ b → 0 ≤ Λ → IntegrableOn f (Icc a b) → (∀ s ∈ Icc a b, f s ≤ C + Λ * ∫ τ in Ioc s b, f τ) → ∀ s ∈ Icc a b, f s ≤ C * Real.exp (Λ * (b - s))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
