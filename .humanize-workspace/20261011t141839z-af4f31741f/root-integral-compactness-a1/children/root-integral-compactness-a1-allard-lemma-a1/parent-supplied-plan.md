# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1`
- Child key: `allard_lemma`
- Declaration: `Submission.intcpt_allard_integrality_lemma`
- Exact Lean type: `MonotonicityFormula → ∀ (N n : ℕ) (Λ : ℝ), 1 ≤ n → 1 ≤ Λ → ∃ δbar c₀ : ℝ, 0 < δbar ∧ 0 ≤ c₀ ∧ ∀ δ ε : ℝ, 0 < δ → δ ≤ δbar → 0 < ε → ε ≤ δ ^ 4 → ∀ (U : Set (Euclidean N)) (W : Varifold N n U) (P : Grassmannian N n), ball (0 : Euclidean N) 3 ⊆ U → W.HasLocallyBoundedFirstVariation → W.weight (ball (0 : Euclidean N) 3) ≤ ENNReal.ofReal Λ → variationMeasure W (ball (0 : Euclidean N) 3) < ENNReal.ofReal (ε ^ 2) → (∫⁻ z in ball (0 : Euclidean N) 3 ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) < ENNReal.ofReal (ε ^ 2) → W.weight {y | y ∈ closedBall (0 : Euclidean N) 2 ∧ y ∈ W.weight.support ∧ ¬ ((∀ ρ : ℝ, 0 < ρ → ρ < 1 → variationMeasure W (closedBall y ρ) ≤ ENNReal.ofReal ε * W.weight (closedBall y ρ)) ∧ (∀ ρ : ℝ, 0 < ρ → ρ < 1 → (∫⁻ z in closedBall y ρ ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) ≤ ENNReal.ofReal (ε * ρ ^ n)))} ≤ ENNReal.ofReal (c₀ * ε) ∧ ∀ (x : Euclidean N) (s : Finset (Euclidean N)) (Θ : Euclidean N → ℝ≥0∞), x ∈ P.plane → ‖x‖ < 1 → (∀ y ∈ s, Grassmannian.project P y = x ∧ y ∈ closedBall (0 : Euclidean N) 2 ∧ y ∈ W.weight.support ∧ (∀ ρ : ℝ, 0 < ρ → ρ < 1 → variationMeasure W (closedBall y ρ) ≤ ENNReal.ofReal ε * W.weight (closedBall y ρ)) ∧ (∀ ρ : ℝ, 0 < ρ → ρ < 1 → (∫⁻ z in closedBall y ρ ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) ≤ ENNReal.ofReal (ε * ρ ^ n)) ∧ ‖y - Grassmannian.project P y‖ < ε ∧ HasDensity n W.weight y (Θ y) ∧ 1 ≤ Θ y) → ∑ y ∈ s, Θ y ≤ ENNReal.ofReal (1 + δ) * W.weight (closedBall x 1) / unitBallVolume n + ENNReal.ofReal δ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
