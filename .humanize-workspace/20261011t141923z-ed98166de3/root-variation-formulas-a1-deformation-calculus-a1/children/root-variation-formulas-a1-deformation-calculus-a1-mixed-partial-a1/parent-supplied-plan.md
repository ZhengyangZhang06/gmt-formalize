# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.variation_formulas-a1.deformation_calculus-a1.mixed_partial-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-deformation-calculus-a1-mixed-partial-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.variation_formulas-a1.deformation_calculus-a1`
- Child key: `mixed_partial`
- Declaration: `Submission.variation_deformation_mixed_partial`
- Exact Lean type: `∀ (N : ℕ) (Φ : ℝ → Rn N → Rn N) (t : ℝ) (y : Rn N), ContDiffAt ℝ 2 (fun p : ℝ × Rn N ↦ Φ p.1 p.2) (t, y) → HasDerivAt (fun s ↦ fderiv ℝ (Φ s) y) (fderiv ℝ (fun x ↦ deriv (fun s ↦ Φ s x) t) y) t`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
