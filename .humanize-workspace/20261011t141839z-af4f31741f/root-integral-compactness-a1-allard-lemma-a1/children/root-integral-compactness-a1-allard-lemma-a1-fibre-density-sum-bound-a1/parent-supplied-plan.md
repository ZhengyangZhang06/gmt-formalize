# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.fibre_density_sum_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-fibre-density-sum-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1`
- Child key: `fibre_density_sum_bound`
- Declaration: `Submission.intcpt_allard_fibre_density_sum_bound`
- Exact Lean type: `MonotonicityFormula → ∀ (N n : ℕ) (Λ : ℝ), 1 ≤ Λ → ∀ M : ℕ, ∃ δ' : ℝ, 0 < δ' ∧ ∀ δ ε : ℝ, 0 < δ → δ ≤ δ' → 0 < ε → ε ≤ δ ^ 4 → ∀ (U : Set (Euclidean N)) (W : Varifold N n U) (P : Grassmannian N n), ball (0 : Euclidean N) 3 ⊆ U → W.HasLocallyBoundedFirstVariation → W.weight (ball (0 : Euclidean N) 3) ≤ ENNReal.ofReal Λ → ∀ (x : Euclidean N) (s : Finset (Euclidean N)) (Θ : Euclidean N → ℝ≥0∞), s.card ≤ M → (∀ y ∈ s, Grassmannian.project P y = x ∧ y ∈ closedBall (0 : Euclidean N) 2 ∧ (∀ ρ : ℝ, 0 < ρ → ρ < 1 → variationMeasure W (closedBall y ρ) ≤ ENNReal.ofReal ε * W.weight (closedBall y ρ)) ∧ (∀ ρ : ℝ, 0 < ρ → ρ < 1 → (∫⁻ z in closedBall y ρ ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) ≤ ENNReal.ofReal (ε * ρ ^ n)) ∧ ‖y - Grassmannian.project P y‖ < ε ∧ HasDensity n W.weight y (Θ y)) → ∑ y ∈ s, Θ y ≤ ENNReal.ofReal (1 + δ) * W.weight (closedBall x 1) / unitBallVolume n + ENNReal.ofReal δ`

## Sibling prerequisites

- `root.integral_compactness-a1.allard_lemma-a1.good_point_monotonicity-a1`
- `root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1`
- `root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
