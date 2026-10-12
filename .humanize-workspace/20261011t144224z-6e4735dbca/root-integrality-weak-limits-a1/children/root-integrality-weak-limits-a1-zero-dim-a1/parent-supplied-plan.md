# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.zero_dim-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-zero-dim-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1`
- Child key: `zero_dim`
- Declaration: `Submission.iwl_zero_dim_integrality`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (Xj : ℕ → GeometricCurrentOn U 0) (X : GeometricCurrentOn U 0), (∀ j, IsIntegerMultiplicity (Xj j)) → (∀ W, CompactlyContainedOpen W U → (⨆ j, (Xj j).massOn W) < ∞) → WeaklyConvergesOn Xj X → IsIntegerMultiplicity X`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.patching-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
