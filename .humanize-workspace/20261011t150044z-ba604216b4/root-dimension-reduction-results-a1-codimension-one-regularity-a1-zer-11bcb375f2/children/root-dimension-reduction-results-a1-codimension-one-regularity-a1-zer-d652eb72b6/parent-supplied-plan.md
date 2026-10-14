# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1.local_comparison-a1.sandwich-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-d652eb72b6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1.local_comparison-a1`
- Child key: `sandwich`
- Declaration: `Submission.codim1_zsl_ga_lc_sandwich`
- Exact Lean type: `∀ (m : ℕ) (t ε c : ℝ) (X H I : ℝ≥0∞), ε < 1 → 0 ≤ c → (1 + ε) ^ m ≤ t * (1 - ε) → 1 + ε ≤ t * (1 - ε) ^ m → ENNReal.ofReal ((1 - ε) ^ m) * (ENNReal.ofReal c * X) ≤ H → H ≤ ENNReal.ofReal ((1 + ε) ^ m) * (ENNReal.ofReal c * X) → ENNReal.ofReal ((1 - ε) * c) * X ≤ I → I ≤ ENNReal.ofReal ((1 + ε) * c) * X → H ≤ ENNReal.ofReal t * I ∧ I ≤ ENNReal.ofReal t * H`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
