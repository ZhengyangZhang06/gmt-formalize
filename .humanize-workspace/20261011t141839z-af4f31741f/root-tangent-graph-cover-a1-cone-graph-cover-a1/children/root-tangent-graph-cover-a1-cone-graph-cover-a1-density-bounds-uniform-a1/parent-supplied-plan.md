# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_graph_cover-a1.cone_graph_cover-a1.density_bounds_uniform-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-tangent-graph-cover-a1-cone-graph-cover-a1-density-bounds-uniform-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_graph_cover-a1.cone_graph_cover-a1`
- Child key: `density_bounds_uniform`
- Declaration: `Submission.tgc_eventual_density_bounds_uniform`
- Exact Lean type: `∀ (n : ℕ) (β : ℝ) (F G : ℝ → ℝ≥0∞), 0 < β → (∃ c : ℝ≥0∞, 0 < c ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), c * ENNReal.ofReal t ^ n ≤ F t) → (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), G t ≤ ε * ENNReal.ofReal t ^ n) → ∃ m k : ℕ, ∀ t : ℝ, 0 < t → t ≤ 1 / ((k : ℝ) + 1) → ENNReal.ofReal (1 / ((m : ℝ) + 1) * t ^ n) ≤ F t ∧ G t ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1) * β * t ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
