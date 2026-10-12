# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.varifold_tangents-a1.density_lower_bound-a1.density_pullback-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-density-lower-bound-a1-density-pullback-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.varifold_tangents-a1.density_lower_bound-a1`
- Child key: `density_pullback`
- Declaration: `Submission.varifold_tangents_dlb_ae_hasDensity_of_restricted`
- Exact Lean type: `∀ (N n : ℕ) (U Ω : Set (Euclidean N)) (V : Varifold N n U) (W : Varifold N n Ω) (c : ℝ≥0∞), c ≠ 0 → c ≠ ∞ → W.measure = c • V.measure.restrict (Ω ×ˢ (univ : Set (Grassmannian N n))) → (∀ᵐ y ∂W.weight, ∃ θ : ℝ≥0∞, HasDensity n W.weight y θ ∧ 1 ≤ θ) → ∀ᵐ y ∂V.weight, y ∈ Ω → ∃ θ : ℝ≥0∞, HasDensity n V.weight y θ ∧ c⁻¹ ≤ θ`

## Sibling prerequisites

- `root.varifold_tangents-a1.density_lower_bound-a1.density_scaling-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
