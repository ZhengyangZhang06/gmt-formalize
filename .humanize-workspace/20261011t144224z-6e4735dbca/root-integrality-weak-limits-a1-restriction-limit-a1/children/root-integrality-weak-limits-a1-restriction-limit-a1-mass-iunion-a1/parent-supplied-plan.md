# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.restriction_limit-a1.mass_iunion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-restriction-limit-a1-mass-iunion-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.restriction_limit-a1`
- Child key: `mass_iunion`
- Declaration: `Submission.iwl_rl_massOn_iUnion_monotone`
- Exact Lean type: `∀ (P k : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U k) (O : ℕ → Set (Eucl P)), (∀ i, IsOpen (O i)) → Monotone O → T.massOn (⋃ i, O i) = ⨆ i, T.massOn (O i)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
