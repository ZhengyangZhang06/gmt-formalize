# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ff027afbd6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1`
- Child key: `class_reduction`
- Declaration: `Submission.idtp_fons_flat_class_reduction`
- Exact Lean type: `∀ (P n : ℕ) (Λ : ℝ) (𝓜 : Set (Measure (Euclid P))) (D : Measure (Euclid P) → Set (Euclid P)) (dens : Measure (Euclid P) → Euclid P → ℝ), 1 ≤ n → (∀ (μ : Measure (Euclid P)) (x : Euclid P), dens μ x = (limsup (fun ρ : ℝ => μ (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)).toReal) → (∀ μ ∈ 𝓜, ∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞) → (∀ μ ∈ 𝓜, μ = (μHE[n] : Measure (Euclid P)).withDensity (fun x => ENNReal.ofReal (dens μ x))) → (∀ μ ∈ 𝓜, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → ENNReal.ofReal (lam⁻¹ ^ n) • μ.map (dilation y lam) ∈ 𝓜 ∧ D (ENNReal.ofReal (lam⁻¹ ^ n) • μ.map (dilation y lam)) = dilation y lam '' D μ) → (∀ μ ∈ 𝓜, ∀ y : Euclid P, ‖y‖ < 1 → ∀ lams : ℕ → ℝ, (∀ j, 0 < lams j) → StrictAnti lams → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (ν : Measure (Euclid P)), StrictMono sub ∧ ν ∈ 𝓜 ∧ (∀ t : ℝ, 0 < t → ∀ w : Euclid P, dens ν (t • w) = dens ν w) ∧ ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun j => ∫ x, f x ∂(ENNReal.ofReal ((lams (sub j))⁻¹ ^ n) • μ.map (dilation y (lams (sub j))))) atTop (𝓝 (∫ x, f x ∂ν))) → (∀ μ ∈ 𝓜, IsOpen (D μ) ∧ ball (0 : Euclid P) 2 ⊆ D μ) → (∀ μ ∈ 𝓜, ∀ μs : ℕ → Measure (Euclid P), (∀ j, μs j ∈ 𝓜) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun j => ∫ x, f x ∂(μs j)) atTop (𝓝 (∫ x, f x ∂μ))) → ∀ K : Set (Euclid P), IsCompact K → K ⊆ D μ → ∀ᶠ j in atTop, K ⊆ D (μs j)) → (∀ μ ∈ 𝓜, ∀ (y : Euclid P) (ρ : ℝ), 0 < ρ → closedBall y ρ ⊆ D μ → (∀ ε : ℝ, 0 < ε → μ (ball y ε) ≠ 0) → ENNReal.ofReal (Real.exp (-(Λ * ρ))) * (unitBallVolume n * ENNReal.ofReal (ρ ^ n)) ≤ μ (ball y ρ)) → (∀ ν ∈ 𝓜, ∀ L : Submodule ℝ (Euclid P), Module.finrank ℝ L + 1 = n → (∀ y ∈ L, ∀ t : ℝ, 0 < t → ∀ w : Euclid P, dens ν (y + t • w) = dens ν w) → ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n ∧ ∀ w : Euclid P, (∀ ε : ℝ, 0 < ε → ν (ball w ε) ≠ 0) → w ∈ Q) → (∀ ν ∈ 𝓜, (∀ t : ℝ, 0 < t → ∀ w : Euclid P, dens ν (t • w) = dens ν w) → D ν = univ) → ∀ μ ∈ 𝓜, ∀ β : ℝ, 0 < β → ∃ Z : Set (Euclid P), (n = 1 → Z = ∅) ∧ (∀ α : ℝ, 0 < α → μH[(n : ℝ) - 2 + α] Z = 0) ∧ ∀ w ∈ ball (0 : Euclid P) 1, (∀ ε : ℝ, 0 < ε → μ (ball w ε) ≠ 0) → w ∉ Z → ∃ ρ : ℝ, 0 < ρ ∧ ball w ρ ⊆ D μ ∧ ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n ∧ ∃ s : ℝ, s < β * ρ ∧ ∀ y : Euclid P, (∀ ε : ℝ, 0 < ε → μ (ball y ε) ≠ 0) → y ∈ ball w ρ → ‖(y - w) - Q.starProjection (y - w)‖ ≤ s`

## Sibling prerequisites

- `root.abstract_dimension_reduction-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
