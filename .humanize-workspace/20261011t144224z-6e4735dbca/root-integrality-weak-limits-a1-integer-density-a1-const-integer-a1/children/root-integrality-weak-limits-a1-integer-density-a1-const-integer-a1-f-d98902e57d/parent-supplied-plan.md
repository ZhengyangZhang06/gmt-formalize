# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.const_integer-a1.frame_sign_top-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-const-integer-a1-f-d98902e57d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.const_integer-a1`
- Child key: `frame_sign_top`
- Declaration: `Submission.ind_top_orthonormal_frame_sign`
- Exact Lean type: `∀ (n : ℕ) (τ : Fin n → Eucl n), Orthonormal ℝ τ → simpleNVector τ = simpleNVector (fun i => EuclideanSpace.single i (1 : ℝ)) ∨ simpleNVector τ = -simpleNVector (fun i => EuclideanSpace.single i (1 : ℝ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
