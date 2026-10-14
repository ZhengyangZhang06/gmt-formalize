# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.projection_null-a1.covector_rotated_expansion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-covector-rotated-expansion-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.projection_null-a1`
- Child key: `covector_rotated_expansion`
- Declaration: `Submission.rpn_covector_rotated_expansion`
- Exact Lean type: `∀ (P n : ℕ) (Q : Eucl P ≃ₗᵢ[ℝ] Eucl P) (φ : Covector (Eucl P) n), φ = ∑ α : SimonMultiIndex n P, φ (fun i => Q.symm (EuclideanSpace.single (α i) (1 : ℝ))) • wedgeCovectors n (fun i => (EuclideanSpace.proj (α i) : Eucl P →L[ℝ] ℝ).comp (Q : Eucl P →L[ℝ] Eucl P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
