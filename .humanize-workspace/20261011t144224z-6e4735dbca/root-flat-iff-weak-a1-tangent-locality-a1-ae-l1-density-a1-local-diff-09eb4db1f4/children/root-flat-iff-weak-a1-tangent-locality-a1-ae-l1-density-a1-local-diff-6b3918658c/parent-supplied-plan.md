# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.local_differentiation-a1.weighted_lebesgue_point-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-ae-l1-density-a1-local-diff-6b3918658c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.local_differentiation-a1`
- Child key: `weighted_lebesgue_point`
- Declaration: `Submission.fiw_tl_ald_ld_weighted_lebesgue_point`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Eucl P)) (M : Set (Eucl P)) (θ f : Eucl P → ℝ) (y : Eucl P) (r : ℝ), NullMeasurableSet M μ → (∀ z ∈ M, 0 < θ z) → IntegrableOn θ (M ∩ closedBall y r) μ → IntegrableOn (fun z => θ z * f z) (M ∩ closedBall y r) μ → ∀ᵐ x ∂(μ.restrict (M ∩ ball y r)), Tendsto (fun s : ℝ => (∫⁻ z in M ∩ closedBall x s, ENNReal.ofReal (θ z) * ‖f z - f x‖ₑ ∂μ) / (∫⁻ z in M ∩ closedBall x s, ENNReal.ofReal (θ z) ∂μ)) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
