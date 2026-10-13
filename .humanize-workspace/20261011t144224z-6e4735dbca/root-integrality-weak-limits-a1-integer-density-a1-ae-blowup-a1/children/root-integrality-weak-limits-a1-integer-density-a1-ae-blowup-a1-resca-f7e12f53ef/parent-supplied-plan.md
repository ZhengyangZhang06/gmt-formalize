# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1.rescaled_tangent_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-ae-blowup-a1-resca-f7e12f53ef/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1`
- Child key: `rescaled_tangent_limit`
- Declaration: `Submission.ind_ab_rescaled_tangent_limit`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P) (Q : Submodule ℝ (Eucl P)) (f : Eucl P → ℝ), HasWeightedApproximateTangentSpaceAt n M θ x Q → Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ y in M, θ y * f (r⁻¹ • (y - x)) ∂(μHE[n] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 (θ x * ∫ z in (Q : Set (Eucl P)), f z ∂(μHE[n] : Measure (Eucl P))))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
