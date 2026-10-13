# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1.countable_separating_tests-a1.plateau_weak_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-978ddf2bae/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.alpha_homogeneous-a1.countable_separating_tests-a1`
- Child key: `plateau_weak_limit`
- Declaration: `Submission.idtp_cse_ah_cst_plateau_weak_limit`
- Exact Lean type: `∀ p q : ℝ, ∃ χ : ℕ → ℝ → ℝ, (∀ k, ContDiff ℝ 1 (χ k)) ∧ (∀ k, tsupport (χ k) ⊆ Icc p q) ∧ ∀ g : ℝ → ℝ, Integrable g → Tendsto (fun k => ∫ α, χ k α * g α) atTop (𝓝 (∫ α in Ioo p q, g α))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
