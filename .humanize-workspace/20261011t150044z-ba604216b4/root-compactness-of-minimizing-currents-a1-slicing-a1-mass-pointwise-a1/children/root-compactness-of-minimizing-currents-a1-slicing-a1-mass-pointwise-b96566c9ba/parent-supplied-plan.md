# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.slicing-a1.mass_pointwise-a1.liminf_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-mass-pointwise-b96566c9ba/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.slicing-a1.mass_pointwise-a1`
- Child key: `liminf_bound`
- Declaration: `Submission.cmcs_smp_liminf_bound`
- Exact Lean type: `∀ (L : NNReal) (z : ℝ) (Φ : ℝ → ℝ) (v : ℝ → ℝ≥0∞), Tendsto Φ (𝓝[>] 0) (𝓝 z) → (∀ h : ℝ, 0 < h → h < 1 → ENNReal.ofReal |Φ h| ≤ ENNReal.ofReal ((L : ℝ) / (h * (1 - h / 2))) * v h) → ENNReal.ofReal z ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * v h) (𝓝[>] 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
