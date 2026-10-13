# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.fibre_density_sum_bound-a1.density_cylinder_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-fibre-density-sum-bound-729fe6787f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1.fibre_density_sum_bound-a1`
- Child key: `density_cylinder_bound`
- Declaration: `Submission.intcpt_allard_fdsb_density_cylinder_bound`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) (P : Grassmannian N n) (y : Euclidean N) (θ : ℝ≥0∞) (ε K : ℝ), 0 ≤ ε → Real.exp ε ≤ 2 → 0 ≤ K → (∀ σ : ℝ, 0 < σ → σ < 1 → θ ≤ ENNReal.ofReal (Real.exp (ε * σ)) * densityRatio n μ y σ) → (∀ τ σ ρ : ℝ, 0 < τ → τ ≤ 1 → 0 < σ → σ ≤ ρ → ρ < 1 → μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) / ENNReal.ofReal ρ ^ n + ENNReal.ofReal (K * ε * ρ / τ)) → ∀ τ σ : ℝ, 0 < τ → τ ≤ 1 / 4 → 0 < σ → σ < 1 → θ ≤ (ENNReal.ofReal (Real.exp ε) * (μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 4 * τ}) / ENNReal.ofReal σ ^ n) + ENNReal.ofReal (K * ε * σ / τ)) / unitBallVolume n`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
