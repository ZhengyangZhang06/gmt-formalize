# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_tangent-a1.lebesgue_rescaled-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-57d04995e6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_tangent-a1`
- Child key: `lebesgue_rescaled`
- Declaration: `Submission.doraggt_ae_rescaled_lebesgue_point`
- Exact Lean type: `∀ (n : ℕ) (g : Euclid n → ℝ), LocallyIntegrable g volume → ∀ᵐ v ∂(volume : Measure (Euclid n)), ∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ∫ w in closedBall (0 : Euclid n) R, |g (v + r • w) - g v|) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
