# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_local_antilipschitz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-fa0007faad/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1`
- Child key: `c1_local_antilipschitz`
- Declaration: `Submission.lpf_c1_local_antilipschitz`
- Exact Lean type: `∀ (n Q : ℕ) (G : Eucl n → Eucl Q) (w : Eucl n), ContDiff ℝ 1 G → Function.Injective (fderiv ℝ G w) → ∃ r : ℝ, 0 < r ∧ ∃ c : ℝ, 0 < c ∧ ∀ z ∈ ball w r, ∀ z' ∈ ball w r, c * ‖z - z'‖ ≤ ‖G z - G z'‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
