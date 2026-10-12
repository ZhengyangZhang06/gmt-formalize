# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_campanato-a1.lipschitz_ae_derivative-a1.lipschitz_ftc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-lipschitz-ae-derivative-73a473832b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.graph_campanato-a1.lipschitz_ae_derivative-a1`
- Child key: `lipschitz_ftc`
- Declaration: `Submission.allard52_lad_lipschitz_ftc`
- Exact Lean type: `∀ (ℓ : ℕ) (φ k : ℝ → Rn ℓ) (a b : ℝ) (L : ℝ≥0), a ≤ b → LipschitzOnWith L φ (Icc a b) → ContinuousOn k (Icc a b) → (∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → HasDerivAt φ (k t) t) → φ b - φ a = ∫ t in a..b, k t`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
