# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.tangent_locality-a1.growth_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-growth-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.tangent_locality-a1`
- Child key: `growth_bound`
- Declaration: `Submission.fiw_tl_growth_bound`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P) (ρ : ℝ) (Q : Submodule ℝ (Eucl P)), 0 < ρ → NullMeasurableSet M (μHE[n] : Measure (Eucl P)) → (∀ y ∈ M, 0 ≤ θ y) → IntegrableOn θ (M ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) → HasWeightedApproximateTangentSpaceAt n M θ x Q → ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (0 : ℝ), ∫⁻ z in M ∩ closedBall x s, ENNReal.ofReal (θ z) ∂(μHE[n] : Measure (Eucl P)) ≤ ENNReal.ofReal (C * s ^ n)`

## Sibling prerequisites

- `root.flat_iff_weak-a1.tangent_locality-a1.blowup_change_of_variables-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
