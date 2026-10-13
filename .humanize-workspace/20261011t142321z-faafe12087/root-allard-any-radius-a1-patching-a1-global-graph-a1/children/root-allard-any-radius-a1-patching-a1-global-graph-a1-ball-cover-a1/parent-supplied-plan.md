# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.patching-a1.global_graph-a1.ball_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1-global-graph-a1-ball-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.patching-a1.global_graph-a1`
- Child key: `ball_cover`
- Declaration: `Submission.arp_ball_subset_of_closed_rel_open`
- Exact Lean type: `∀ {m : ℕ} (D : Set (Rn m)) (c : Rn m) (R : ℝ), 0 < R → IsClosed D → c ∈ D → (∀ w ∈ D ∩ ball c R, ∃ ε : ℝ, 0 < ε ∧ ball w ε ∩ ball c R ⊆ D) → ball c R ⊆ D`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
