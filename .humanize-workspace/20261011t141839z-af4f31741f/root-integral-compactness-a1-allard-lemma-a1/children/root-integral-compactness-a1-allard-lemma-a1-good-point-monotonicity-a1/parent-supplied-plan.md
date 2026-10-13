# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.good_point_monotonicity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-good-point-monotonicity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1`
- Child key: `good_point_monotonicity`
- Declaration: `Submission.intcpt_allard_good_point_monotonicity`
- Exact Lean type: `MonotonicityFormula → ∀ (N n : ℕ) (U : Set (Euclidean N)) (W : Varifold N n U) (y : Euclidean N) (ε Λ : ℝ), W.HasLocallyBoundedFirstVariation → ball y 1 ⊆ U → 0 ≤ ε → W.weight (ball y 1) ≤ ENNReal.ofReal Λ → (∀ ρ : ℝ, 0 < ρ → ρ < 1 → variationMeasure W (closedBall y ρ) ≤ ENNReal.ofReal ε * W.weight (closedBall y ρ)) → MonotoneOn (fun ρ : ℝ ↦ ENNReal.ofReal (Real.exp (ε * ρ)) * W.weight (closedBall y ρ) / ENNReal.ofReal ρ ^ n) (Ioo 0 1) ∧ (∃ θ : ℝ≥0∞, HasDensity n W.weight y θ ∧ θ ≠ ∞ ∧ ∀ σ : ℝ, 0 < σ → σ < 1 → θ ≤ ENNReal.ofReal (Real.exp (ε * σ)) * densityRatio n W.weight y σ) ∧ ∀ σ : ℝ, 0 < σ → σ < 1 → W.weight (closedBall y σ) ≤ ENNReal.ofReal (Real.exp ε * Λ * σ ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
