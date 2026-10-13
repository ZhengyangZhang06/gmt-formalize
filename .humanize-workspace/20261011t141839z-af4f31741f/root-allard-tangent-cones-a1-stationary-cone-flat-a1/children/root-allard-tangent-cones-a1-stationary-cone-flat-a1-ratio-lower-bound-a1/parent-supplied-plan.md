# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.stationary_cone_flat-a1.ratio_lower_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-stationary-cone-flat-a1-ratio-lower-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1.stationary_cone_flat-a1`
- Child key: `ratio_lower_bound`
- Declaration: `Submission.allard_tc_scf_ratio_ge_on_support`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) (a : ℝ≥0∞), (∀ (y : Euclidean N) (ρ : ℝ), μ (closedBall y ρ) ≠ ∞) → (∀ y : Euclidean N, MonotoneOn (densityRatio n μ y) (Ioi 0)) → (∀ᵐ y ∂μ, ∃ θ : ℝ≥0∞, HasDensity n μ y θ ∧ a ≤ θ) → ∀ y ∈ μ.support, ∀ ρ : ℝ, 0 < ρ → a ≤ densityRatio n μ y ρ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
