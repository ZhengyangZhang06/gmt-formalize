# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.variation_formulas-a1.deformation_calculus-a1.partials_contdiffon-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-deformation-calculus-a1-partials-contdiffon-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.variation_formulas-a1.deformation_calculus-a1`
- Child key: `partials_contdiffon`
- Declaration: `Submission.variation_deformation_partials_contDiffOn`
- Exact Lean type: `∀ (N : ℕ) (Φ : ℝ → Rn N → Rn N) (O : Set (ℝ × Rn N)) (m n : WithTop ℕ∞), IsOpen O → ContDiffOn ℝ n (fun p : ℝ × Rn N ↦ Φ p.1 p.2) O → m + 1 ≤ n → ContDiffOn ℝ m (fun p : ℝ × Rn N ↦ fderiv ℝ (Φ p.1) p.2) O ∧ ContDiffOn ℝ m (fun p : ℝ × Rn N ↦ deriv (fun s ↦ Φ s p.2) p.1) O`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
