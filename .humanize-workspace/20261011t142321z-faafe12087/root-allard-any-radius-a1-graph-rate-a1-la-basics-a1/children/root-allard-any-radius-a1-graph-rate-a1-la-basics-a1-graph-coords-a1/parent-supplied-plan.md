# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.graph_rate-a1.la_basics-a1.graph_coords-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-la-basics-a1-graph-coords-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.graph_rate-a1.la_basics-a1`
- Child key: `graph_coords`
- Declaration: `Submission.any_radius_gr_la_graphPoint_algebra`
- Exact Lean type: `∀ (n ℓ : ℕ), (∀ (a : Rn n) (b : Rn ℓ) (i : Fin n), graphPoint a b (Fin.castAdd ℓ i) = a i) ∧ (∀ (a : Rn n) (b : Rn ℓ) (j : Fin ℓ), graphPoint a b (Fin.natAdd n j) = b j) ∧ (∀ (a a' : Rn n) (b b' : Rn ℓ), graphPoint (a + a') (b + b') = graphPoint a b + graphPoint a' b') ∧ (∀ (a a' : Rn n) (b b' : Rn ℓ), graphPoint (a - a') (b - b') = graphPoint a b - graphPoint a' b') ∧ (∀ (t : ℝ) (a : Rn n) (b : Rn ℓ), graphPoint (t • a) (t • b) = t • graphPoint a b) ∧ (∀ (a : Rn n) (b : Rn ℓ), ‖graphPoint a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2) ∧ (∀ (a a' : Rn n) (b b' : Rn ℓ), inner ℝ (graphPoint a b) (graphPoint a' b') = inner ℝ a a' + inner ℝ b b')`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
