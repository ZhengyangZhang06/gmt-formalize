# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.curvature_monotonicity-a1.density_usc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-curvature-monotonicity-a1-density-usc-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.curvature_monotonicity-a1`
- Child key: `density_usc`
- Declaration: `Submission.mcm_density_usc_of_monotone`
- Exact Lean type: `∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)), IsFiniteMeasureOnCompacts V.weight → (∀ ξ ∈ U, ∃ r : ℝ, 0 < r ∧ ∃ c : ℝ → ℝ, Tendsto c (𝓝[>] 0) (𝓝 0) ∧ ∀ η ∈ ball ξ r, ∃ F E : ℝ → ℝ, (∀ ρ ∈ Ioo 0 r, F ρ ∈ Icc (Real.exp (-c ρ)) (Real.exp (c ρ)) ∧ |E ρ| ≤ c ρ) ∧ MonotoneOn (fun ρ ↦ F ρ * (V.weight.real (closedBall η ρ) / ρ ^ n) + E ρ) (Ioo 0 r)) → (∀ ξ ∈ U, V.HasDensityAt ξ (V.density ξ)) ∧ UpperSemicontinuousOn V.density U`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
