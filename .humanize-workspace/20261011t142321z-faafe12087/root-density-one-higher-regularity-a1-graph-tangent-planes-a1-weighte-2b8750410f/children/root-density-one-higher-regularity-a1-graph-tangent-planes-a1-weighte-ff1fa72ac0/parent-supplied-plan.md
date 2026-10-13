# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.graph_tangent_planes-a1.weighted_tangent_pointwise-a1.rescaled_density_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1-weighte-ff1fa72ac0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1.weighted_tangent_pointwise-a1`
- Child key: `rescaled_density_limit`
- Declaration: `Submission.dohr_tp_wtlp_rescaled_limit`
- Exact Lean type: `∀ (n : ℕ) (L : ℝ → ℝ≥0∞) (ρ : ℝ), 0 < ρ → Tendsto (fun t : ℝ => ENNReal.ofReal ((t ^ n)⁻¹) * L t) (𝓝[>] 0) (𝓝 0) → (∀ᶠ r in 𝓝[>] (0 : ℝ), L (r * ρ) ≠ ⊤) ∧ Tendsto (fun r : ℝ => (r ^ n)⁻¹ * (L (r * ρ)).toReal) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
