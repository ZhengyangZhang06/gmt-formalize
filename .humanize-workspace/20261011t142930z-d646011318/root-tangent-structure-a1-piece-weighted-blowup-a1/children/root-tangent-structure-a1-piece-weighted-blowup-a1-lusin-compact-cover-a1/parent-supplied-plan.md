# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.piece_weighted_blowup-a1.lusin_compact_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-weighted-blowup-a1-lusin-compact-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.piece_weighted_blowup-a1`
- Child key: `lusin_compact_cover`
- Declaration: `Submission.ts_pwb_lusin_compact_cover`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (A : Set (Ambient n ℓ)) (g : Ambient n ℓ → ℝ), NullMeasurableSet A μ → μ A ≠ ⊤ → AEStronglyMeasurable g (μ.restrict A) → ∃ K : ℕ → Set (Ambient n ℓ), (∀ k, IsCompact (K k) ∧ K k ⊆ A ∧ ContinuousOn g (K k)) ∧ μ (A \ ⋃ k, K k) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
