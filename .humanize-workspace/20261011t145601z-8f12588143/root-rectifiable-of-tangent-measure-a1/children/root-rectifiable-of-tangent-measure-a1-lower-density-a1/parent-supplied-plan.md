# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiable_of_tangent_measure-a1.lower_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-rectifiable-of-tangent-measure-a1-lower-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiable_of_tangent_measure-a1`
- Child key: `lower_density`
- Declaration: `Submission.tangentMeasure_eventually_lower_density`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Rn N)) (x : Rn N) (P : Submodule ℝ (Rn N)) (θ : ℝ), (∀ K : Set (Rn N), IsCompact K → μ K < ∞) → 0 < θ → HasApproxTangentPlaneWithMultiplicity n μ x P θ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ENNReal.ofReal (c * ρ ^ n) ≤ μ (Metric.ball x ρ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
