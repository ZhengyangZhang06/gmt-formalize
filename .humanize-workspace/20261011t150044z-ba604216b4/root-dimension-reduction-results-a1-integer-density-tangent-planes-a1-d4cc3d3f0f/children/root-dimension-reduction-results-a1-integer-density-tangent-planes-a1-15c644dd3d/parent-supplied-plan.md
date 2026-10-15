# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1.lower_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-15c644dd3d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1`
- Child key: `lower_bound`
- Declaration: `Submission.idtp_fons_cc_psf_lower_bound`
- Exact Lean type: `∀ (P n : ℕ) (μ μ₀ : Measure (Euclid P)) (z : Euclid P) (r : ℝ), 0 < r → μ₀ = ENNReal.ofReal (r⁻¹ ^ n) • (μ.restrict (ball z (2 * r))).map (dilation z r) → ∀ Λ₀ : ℝ, 0 ≤ Λ₀ → (∀ p : Euclid P, (∀ ε : ℝ, 0 < ε → μ (ball p ε) ≠ 0) → ∀ σ ρ : ℝ, closedBall p ρ ⊆ closedBall z (2 * r) → 0 < σ → σ < ρ → ENNReal.ofReal (Real.exp (-(Λ₀ * σ))) * (unitBallVolume n * ENNReal.ofReal (σ ^ n)) ≤ μ (ball p σ)) → ∀ (x y : Euclid P) (lam ρ : ℝ), 0 < lam → lam ≤ 1 → 0 < ρ → closedBall y ρ ⊆ dilation x lam '' ball 0 2 → (∀ ε : ℝ, 0 < ε → (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) (ball y ε) ≠ 0) → ENNReal.ofReal (Real.exp (-(r * Λ₀ * ρ))) * (unitBallVolume n * ENNReal.ofReal (ρ ^ n)) ≤ (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) (ball y ρ)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1.domain_geometry-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
