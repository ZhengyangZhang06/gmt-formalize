# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_regularity-a1.holder_class-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-holder-class-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_regularity-a1`
- Child key: `holder_class`
- Declaration: `Submission.isHolderCk_one_of_scaledC1AlphaNorm_ne_top`
- Exact Lean type: `∀ {n ℓ : ℕ} (u : Rn n → Rn ℓ) (B W : Set (Rn n)) (α ρ : ℝ), 0 < α → 0 < ρ → ContDiffOn ℝ 1 u B → W ⊆ interior B → scaledC1AlphaNorm u B α ρ ≠ ∞ → IsHolderCkα 1 α u W`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
