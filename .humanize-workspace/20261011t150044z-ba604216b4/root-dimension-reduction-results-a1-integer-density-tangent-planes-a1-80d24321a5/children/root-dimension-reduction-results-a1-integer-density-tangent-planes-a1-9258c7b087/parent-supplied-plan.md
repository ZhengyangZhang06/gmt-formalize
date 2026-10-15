# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1.uniform_density_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-9258c7b087/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1`
- Child key: `uniform_density_bound`
- Declaration: `Submission.idod_uniform_ball_mass_bound`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (K K'' : Set (Euclid P)) (Λ σ₀ θ₁ θ₂ : ℝ), IsCompact K → 0 ≤ Λ → 0 < σ₀ → θ₁ < θ₂ → (∀ y ∈ K, ∃ θ : ℝ, θ < θ₁ ∧ HasMassDensity T y θ) → (∀ y ∈ K, closedBall y (2 * σ₀) ⊆ K'') → (∀ (y : Euclid P) (R : ℝ), closedBall y R ⊆ K'' → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ y ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → T.massOn (ball y ρ) ≤ ENNReal.ofReal θ₂ * unitBallVolume n * ENNReal.ofReal (ρ ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
