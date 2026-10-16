# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-d4cc3d3f0f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1`
- Child key: `positive_scale_family`
- Declaration: `Submission.idtp_fons_cc_positive_scale_family`
- Exact Lean type: `∀ (P n : ℕ) (μ μ₀ : Measure (Euclid P)) (z : Euclid P) (r : ℝ), 1 ≤ n → 0 < r → μ (ball z (2 * r)) ≠ 0 → μ (ball z (2 * r)) ≠ ∞ → μ₀ = ENNReal.ofReal (r⁻¹ ^ n) • (μ.restrict (ball z (2 * r))).map (dilation z r) → (∀ w ∈ ball (0 : Euclid P) 2, (∀ ε : ℝ, 0 < ε → μ₀ (ball w ε) ≠ 0) ↔ ∀ ε : ℝ, 0 < ε → μ (ball (z + r • w) ε) ≠ 0) ∧ (∀ (x x' : Euclid P) (lam lam' : ℝ), 0 < lam → 0 < lam' → (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) = (ENNReal.ofReal (lam'⁻¹ ^ n) • μ₀.map (dilation x' lam')) → x = x' ∧ lam = lam') ∧ (∀ (x : Euclid P) (lam : ℝ), 0 < lam → (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) univ ≠ 0 ∧ (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) univ ≠ ∞) ∧ (∀ (x : Euclid P) (lam : ℝ), 0 < lam → lam ≤ 1 → ‖x‖ ≤ 1 - lam → IsOpen (dilation x lam '' ball 0 2) ∧ ball 0 2 ⊆ dilation x lam '' ball 0 2) ∧ (∀ (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (ν : Measure (Euclid P)) (K : Set (Euclid P)), (∀ i, 0 < lams i ∧ lams i ≤ 1 ∧ ‖xs i‖ ≤ 1 - lams i) → (∀ K' : Set (Euclid P), IsCompact K' → ν K' ≠ ∞) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun i => ∫ x, f x ∂(ENNReal.ofReal ((lams i)⁻¹ ^ n) • μ₀.map (dilation (xs i) (lams i)))) atTop (𝓝 (∫ x, f x ∂ν))) → IsCompact K → (∀ i, ¬ K ⊆ dilation (xs i) (lams i) '' ball 0 2) → ∃ (x : Euclid P) (lam : ℝ), (0 < lam ∧ lam ≤ 1 ∧ ‖x‖ ≤ 1 - lam) ∧ ν = (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) ∧ ¬ K ⊆ dilation x lam '' ball 0 2) ∧ (∀ (x : Euclid P) (lam : ℝ) (f : Euclid P → ℝ≥0∞), 0 < lam → (∀ t : ℝ, 0 < t → ∀ w : Euclid P, f (t • w) = f w) → (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) ≠ (μHE[n] : Measure (Euclid P)).withDensity f) ∧ ∀ Λ₀ : ℝ, 0 ≤ Λ₀ → (∀ p : Euclid P, (∀ ε : ℝ, 0 < ε → μ (ball p ε) ≠ 0) → ∀ σ ρ : ℝ, closedBall p ρ ⊆ closedBall z (2 * r) → 0 < σ → σ < ρ → ENNReal.ofReal (Real.exp (-(Λ₀ * σ))) * (unitBallVolume n * ENNReal.ofReal (σ ^ n)) ≤ μ (ball p σ)) → ∀ (x y : Euclid P) (lam ρ : ℝ), 0 < lam → lam ≤ 1 → 0 < ρ → closedBall y ρ ⊆ dilation x lam '' ball 0 2 → (∀ ε : ℝ, 0 < ε → (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) (ball y ε) ≠ 0) → ENNReal.ofReal (Real.exp (-(r * Λ₀ * ρ))) * (unitBallVolume n * ENNReal.ofReal (ρ ^ n)) ≤ (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) (ball y ρ)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.ambient_calculus-a1`
- `root.dimension_reduction_results-a1.cone_splitting-a1.measure_invariance-a1.dilate_homogeneity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
