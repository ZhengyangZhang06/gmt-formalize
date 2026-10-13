# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.variation_density_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-variation-density-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1`
- Child key: `variation_density_bound`
- Declaration: `Submission.intcpt_variation_liminf_density_bound`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (μ : Measure (Euclidean N)) (ν : ℕ → Measure (Euclidean N)), IsOpen U → μ Uᶜ = 0 → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → μ K ≠ ∞) → (∀ W : Set (Euclidean N), IsRelCompactOpenIn W U → ⨆ i, ν i W ≠ ∞) → (∀ᵐ x ∂μ, ∃ θ : ℝ≥0∞, HasDensity n μ x θ ∧ θ ≠ ∞) → ∀ᵐ x ∂μ, ∃ c r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r → liminf (fun i ↦ ν i (closedBall x ρ)) atTop ≤ ENNReal.ofReal (c * ρ ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
