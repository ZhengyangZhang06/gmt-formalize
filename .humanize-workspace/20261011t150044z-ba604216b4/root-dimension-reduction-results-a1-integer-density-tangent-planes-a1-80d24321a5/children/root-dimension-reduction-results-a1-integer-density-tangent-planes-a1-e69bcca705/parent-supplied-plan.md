# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1.limit_density_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-e69bcca705/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1`
- Child key: `limit_density_bound`
- Declaration: `Submission.idod_blowUp_limit_mass_density_le`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (z : Euclid P) (r θ₂ ρ₀ : ℝ) (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i), 0 < r → 0 ≤ θ₂ → 0 < ρ₀ → ball z (2 * r) ⊆ U → (∀ y ∈ ball z (3 * r / 2), ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → T.massOn (ball y ρ) ≤ ENNReal.ofReal θ₂ * unitBallVolume n * ENNReal.ofReal (ρ ^ n)) → (∀ i, xs i ∈ ball z r) → Tendsto lams atTop (𝓝 0) → ConvergesWeakly (fun i => blowUp T (xs i) (lams i) (hlams i).ne') S → (∀ (w : Euclid P) (ρ : ℝ), 0 < ρ → S.massOn (ball w ρ) ≤ ENNReal.ofReal θ₂ * unitBallVolume n * ENNReal.ofReal (ρ ^ n)) ∧ ∀ (w : Euclid P) (θ : ℝ), HasMassDensity S w θ → θ ≤ θ₂`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
