# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.submanifold_tangent-a1.tangent_space_eq_range-a1.lift_velocity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-submanifold-tangent-a1-tangent-space-eq-range-a1-lift-velocity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.submanifold_tangent-a1.tangent_space_eq_range-a1`
- Child key: `lift_velocity`
- Declaration: `Submission.simon_lift_velocity_mem_range_fderiv`
- Exact Lean type: `∀ (n N : ℕ) (ψ : Rn n → Rn N) (x₀ : Rn n) (c : ℝ → Rn n) (γ : ℝ → Rn N) (v : Rn N), DifferentiableAt ℝ ψ x₀ → Function.Injective (fderiv ℝ ψ x₀) → Tendsto c (𝓝 (0 : ℝ)) (𝓝 x₀) → (∀ᶠ t in 𝓝 (0 : ℝ), γ t = ψ (c t)) → HasDerivAt γ v 0 → v ∈ LinearMap.range (fderiv ℝ ψ x₀).toLinearMap`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
