# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.infinite_fibres-a1.projection_isometric_chart-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-infinite-fibres-a1-projection-isometric-chart-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.infinite_fibres-a1`
- Child key: `projection_isometric_chart`
- Declaration: `Submission.bf_starProjection_isometricChart`
- Exact Lean type: `∀ (n ℓ : ℕ) (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → ∃ f : Rn (n + ℓ) → Rn n, LipschitzWith 1 f ∧ (∀ a b : Rn (n + ℓ), f a = f b ↔ W.starProjection a = W.starProjection b) ∧ ∀ S : Set (Rn (n + ℓ)), μHE[n] (W.starProjection '' S) = volume (f '' S)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
