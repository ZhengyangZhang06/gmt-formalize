# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_campanato-a1.lipschitz_ae_derivative-a1.segment_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-lipschitz-ae-derivative-946341d9ee/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.graph_campanato-a1.lipschitz_ae_derivative-a1`
- Child key: `segment_null`
- Declaration: `Submission.allard52_lad_segment_null`
- Exact Lean type: `∀ (n : ℕ) (N : Set (Rn n)), volume N = 0 → ∀ (x h : Rn n), ∀ᵐ w ∂(volume : Measure (Rn n)), volume {t : ℝ | x + w + t • h ∈ N} = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
