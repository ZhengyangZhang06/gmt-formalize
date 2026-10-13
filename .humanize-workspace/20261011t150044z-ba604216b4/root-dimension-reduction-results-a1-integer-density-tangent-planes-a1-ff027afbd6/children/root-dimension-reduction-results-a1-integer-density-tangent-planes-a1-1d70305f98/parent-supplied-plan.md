# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1.support_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-1d70305f98/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1`
- Child key: `support_limit`
- Declaration: `Submission.idtp_fons_cr_support_limit`
- Exact Lean type: `∀ (P n : ℕ) (Λ : ℝ) (μ : Measure (Euclid P)) (μs : ℕ → Measure (Euclid P)) (U : Set (Euclid P)) (Ds : ℕ → Set (Euclid P)) (ys : ℕ → Euclid P) (y : Euclid P), (∀ (k : ℕ) (K : Set (Euclid P)), IsCompact K → μs k K ≠ ∞) → IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∀ᶠ k in atTop, K ⊆ Ds k) → (∀ (k : ℕ) (z : Euclid P) (ρ : ℝ), 0 < ρ → closedBall z ρ ⊆ Ds k → (∀ ε : ℝ, 0 < ε → μs k (ball z ε) ≠ 0) → ENNReal.ofReal (Real.exp (-(Λ * ρ))) * (unitBallVolume n * ENNReal.ofReal (ρ ^ n)) ≤ μs k (ball z ρ)) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x ∂(μs k)) atTop (𝓝 (∫ x, f x ∂μ))) → (∀ (k : ℕ) (ε : ℝ), 0 < ε → μs k (ball (ys k) ε) ≠ 0) → Tendsto ys atTop (𝓝 y) → y ∈ U → ∀ ε : ℝ, 0 < ε → μ (ball y ε) ≠ 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
