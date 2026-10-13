# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_semicontinuity-a1.lower_density_ae-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-density-semicontinuity-a1-lower-density-ae-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_semicontinuity-a1`
- Child key: `lower_density_ae`
- Declaration: `Submission.lower_density_ge_one_ae_of_radonConverges`
- Exact Lean type: `MonotonicityFormula → ∀ (N n : ℕ) (U : Set (Euclidean N)) (Vi : ℕ → Varifold N n U) (V : Varifold N n U) (B : ℕ → Set (Euclidean N)), Varifold.RadonConverges Vi V → (∀ i, (Vi i).HasLocallyBoundedFirstVariation) → (∀ W, IsRelCompactOpenIn W U → liminf (fun i ↦ variationMeasure (Vi i) W) atTop ≠ ∞) → (∀ i, ∀ y ∈ U \ B i, ∃ θ : ℝ≥0∞, HasDensity n (Vi i).weight y θ ∧ 1 ≤ θ) → (∀ W, IsRelCompactOpenIn W U → Tendsto (fun i ↦ (Vi i).weight (B i ∩ W)) atTop (𝓝 0)) → ∀ᵐ y ∂V.weight, 1 ≤ liminf (densityRatio n V.weight y) (𝓝[>] 0)`

## Sibling prerequisites

- `root.density_semicontinuity-a1.weight_portmanteau-a1`
- `root.density_semicontinuity-a1.besicovitch_ratio_cover-a1`
- `root.density_semicontinuity-a1.monotonicity_mass_lower_bound-a1`
- `root.density_semicontinuity-a1.limit_mass_lower_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
