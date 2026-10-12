# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.boundary_rectifiability-a1.local_to_global_im-a1.simple_unit_rigidity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-simple-unit-rigidity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.boundary_rectifiability-a1.local_to_global_im-a1`
- Child key: `simple_unit_rigidity`
- Declaration: `Submission.ltg_simple_unit_rigidity`
- Exact Lean type: `∀ (P k : ℕ) (τ τ' : Fin k → Eucl P) (w w' : NVector (Eucl P) k) (a a' : ℝ), Orthonormal ℝ τ → Orthonormal ℝ τ' → (w = simpleNVector τ ∨ w = -simpleNVector τ) → (w' = simpleNVector τ' ∨ w' = -simpleNVector τ') → 0 ≤ a → 0 ≤ a' → a • w = a' • w' → a = a' ∧ (a ≠ 0 → w = w')`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
