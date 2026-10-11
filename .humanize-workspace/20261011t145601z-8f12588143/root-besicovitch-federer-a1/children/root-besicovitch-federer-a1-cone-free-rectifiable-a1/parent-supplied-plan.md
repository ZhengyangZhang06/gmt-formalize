# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_free_rectifiable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-free-rectifiable-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1`
- Child key: `cone_free_rectifiable`
- Declaration: `Submission.bf_coneFree_countablyRectifiable`
- Exact Lean type: `∀ (n ℓ : ℕ) (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → ∀ (s r : ℝ), 0 < s → 0 < r → ∀ E : Set (Rn (n + ℓ)), (∀ a ∈ E, ∀ b ∈ E, dist b a < r → s * ‖b - a‖ ≤ ‖W.starProjection (b - a)‖) → CountablyRectifiable n E`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
