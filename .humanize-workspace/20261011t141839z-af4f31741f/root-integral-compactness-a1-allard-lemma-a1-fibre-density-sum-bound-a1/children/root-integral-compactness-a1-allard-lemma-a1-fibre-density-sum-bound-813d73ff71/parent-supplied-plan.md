# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.fibre_density_sum_bound-a1.one_point_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-fibre-density-sum-bound-813d73ff71/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1.fibre_density_sum_bound-a1`
- Child key: `one_point_bound`
- Declaration: `Submission.intcpt_allard_fdsb_one_point_bound`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) (x y : Euclidean N) (θ : ℝ≥0∞) (δ ε : ℝ), 0 < δ → δ ≤ 1 / 2 → 2 ^ (n + 2) * δ ≤ 1 → 0 < ε → ε ≤ δ ^ 4 → ‖y - x‖ < ε → (∀ σ : ℝ, 0 < σ → σ < 1 → θ ≤ ENNReal.ofReal (Real.exp (ε * σ)) * densityRatio n μ y σ) → θ ≤ ENNReal.ofReal (1 + δ) * μ (closedBall x 1) / unitBallVolume n`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
