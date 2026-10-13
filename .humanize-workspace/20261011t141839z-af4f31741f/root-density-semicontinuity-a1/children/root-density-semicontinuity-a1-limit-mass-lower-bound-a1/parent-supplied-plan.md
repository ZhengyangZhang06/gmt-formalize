# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_semicontinuity-a1.limit_mass_lower_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-density-semicontinuity-a1-limit-mass-lower-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_semicontinuity-a1`
- Child key: `limit_mass_lower_bound`
- Declaration: `Submission.lower_density_ge_one_of_nearby_mass_bounds`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (Vi : ℕ → Varifold N n U) (V : Varifold N n U) (x : Euclidean N) (ρ₀ Λ : ℝ) (q : ℕ → ℕ) (y : ℕ → Euclidean N), Varifold.RadonConverges Vi V → 0 < ρ₀ → ball x ρ₀ ⊆ U → Tendsto q atTop atTop → Tendsto y atTop (𝓝 x) → (∀ i, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → ENNReal.ofReal (Real.exp (-(Λ * ρ))) * unitBallVolume n * ENNReal.ofReal ρ ^ n ≤ (Vi (q i)).weight (closedBall (y i) ρ)) → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → ENNReal.ofReal (Real.exp (-(Λ * ρ))) * unitBallVolume n * ENNReal.ofReal ρ ^ n ≤ V.weight (closedBall x ρ)) ∧ 1 ≤ liminf (densityRatio n V.weight x) (𝓝[>] 0)`

## Sibling prerequisites

- `root.density_semicontinuity-a1.weight_portmanteau-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
