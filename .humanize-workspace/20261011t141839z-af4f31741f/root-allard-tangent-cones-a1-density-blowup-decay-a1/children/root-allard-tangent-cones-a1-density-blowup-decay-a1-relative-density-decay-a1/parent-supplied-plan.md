# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.density_blowup_decay-a1.relative_density_decay-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-density-blowup-decay-a1-relative-density-decay-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1.density_blowup_decay-a1`
- Child key: `relative_density_decay`
- Declaration: `Submission.allard_tc_dbd_relative_decay`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x : Euclidean N) (θ : ℝ≥0∞) (A E : Set (Euclidean N)), HasDensity n μ x θ → θ ≠ ∞ → Tendsto (fun ρ : ℝ ↦ μ (A ∩ closedBall x ρ) / μ (closedBall x ρ)) (𝓝[>] 0) (𝓝 0) → (∀ᵐ y ∂μ, y ∈ E → y ∈ A) → Tendsto (fun ρ : ℝ ↦ μ (closedBall x ρ ∩ E) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
