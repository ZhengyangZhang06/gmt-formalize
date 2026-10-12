# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-integral-density-a1-tangent-point-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.integral_density-a1`
- Child key: `tangent_point_density`
- Declaration: `Submission.intcpt_id_tangent_point_density`
- Exact Lean type: `∀ (N n : ℕ) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ) (x : Euclidean N) (P : Submodule ℝ (Euclidean N)) (r₀ : ℝ), NullMeasurableSet M (μHE[n] : Measure (Euclidean N)) → (∀ y ∈ M, 0 ≤ θ y) → x ∈ M → 0 < r₀ → IntegrableOn θ (M ∩ closedBall x r₀) μHE[n] → Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x P → HasDensity n (((μHE[n] : Measure (Euclidean N)).restrict M).withDensity fun y ↦ ENNReal.ofReal (θ y)) x (ENNReal.ofReal (θ x))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
