# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.c1_graph_density-a1.ratio_squeeze-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-c1-graph-density-a1-ratio-squeeze-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.c1_graph_density-a1`
- Child key: `ratio_squeeze`
- Declaration: `Submission.dohr_ratio_tendsto_one_of_pinching`
- Exact Lean type: `∀ (f : ℝ → ℝ≥0∞) (g : ℝ → ℝ), (∀ δ : ℝ, 0 < δ → ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < g r ∧ ENNReal.ofReal ((1 - δ) * g r) ≤ f r ∧ f r ≤ ENNReal.ofReal ((1 + δ) * g r)) → Tendsto (fun r => f r / ENNReal.ofReal (g r)) (𝓝[>] 0) (𝓝 1)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
