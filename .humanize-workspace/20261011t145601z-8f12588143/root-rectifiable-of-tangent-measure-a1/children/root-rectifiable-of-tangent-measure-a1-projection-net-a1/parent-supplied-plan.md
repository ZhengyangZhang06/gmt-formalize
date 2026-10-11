# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiable_of_tangent_measure-a1.projection_net-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-rectifiable-of-tangent-measure-a1-projection-net-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiable_of_tangent_measure-a1`
- Child key: `projection_net`
- Declaration: `Submission.tangentMeasure_countable_projection_net`
- Exact Lean type: `∀ (N n : ℕ) (ε : ℝ), n ≤ N → 0 < ε → ∃ Q : ℕ → Submodule ℝ (Rn N), (∀ j, finrank ℝ (Q j) = n) ∧ ∀ P : Submodule ℝ (Rn N), finrank ℝ P = n → ∃ j, ‖P.starProjection - (Q j).starProjection‖ < ε`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
