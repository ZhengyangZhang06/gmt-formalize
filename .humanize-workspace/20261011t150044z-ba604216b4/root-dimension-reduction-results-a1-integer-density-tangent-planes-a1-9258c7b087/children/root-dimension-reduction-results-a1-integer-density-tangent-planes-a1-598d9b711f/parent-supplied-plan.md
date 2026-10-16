# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1.uniform_density_bound-a1.nearby_center_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-598d9b711f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.integer_density-a1.uniform_density_bound-a1`
- Child key: `nearby_center_bound`
- Declaration: `Submission.idod_nearby_center_ball_mass_bound`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (y y' : Euclid P) (Λ r τ θ₁ θ₂ : ℝ), 0 ≤ Λ → 0 < τ → τ < r → dist y' y < τ → θ₁ * (r / (r - τ)) ^ n ≤ θ₂ → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball y' ρ)) (Ioo 0 r) → ENNReal.ofReal (Real.exp (Λ * r) / r ^ n) * T.massOn (ball y r) ≤ unitBallVolume n * ENNReal.ofReal θ₁ → ∀ ρ : ℝ, 0 < ρ → ρ < r - τ → T.massOn (ball y' ρ) ≤ ENNReal.ofReal θ₂ * unitBallVolume n * ENNReal.ofReal (ρ ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
