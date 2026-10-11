# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_iff_variational-a1.linear_compact_variation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-stationary-iff-variational-a1-linear-compact-variation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_iff_variational-a1`
- Child key: `linear_compact_variation`
- Declaration: `Submission.exists_isCompactVariation_add_smul`
- Exact Lean type: `∀ (n ℓ : ℕ) (X : Ambient n ℓ → Ambient n ℓ), ContDiff ℝ ∞ X → HasCompactSupport X → ∃ ε : ℝ, IsCompactVariation (fun t y ↦ y + t • X y) ε (tsupport X) ∧ (fun y ↦ deriv (fun t : ℝ ↦ y + t • X y) 0) = X`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
