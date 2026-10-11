# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.local_multiplicity_one-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-local-multiplicity-one-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1`
- Child key: `local_multiplicity_one`
- Declaration: `Submission.dohr_local_multiplicity_one`
- Exact Lean type: `∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p → V.HasGeneralizedMeanCurvature H → V.LocallyLp H p → (∀ᵐ x ∂V.weight, ∃ k : ℕ, 1 ≤ k ∧ V.mult x = k) → ∀ ξ ∈ U, V.HasDensity ξ 1 → ∀ (R : ℝ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), 0 < R → closedBall ξ R ⊆ U → ContDiffOn ℝ 1 u (ball 0 R) → Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R → ∃ s > 0, s ≤ R ∧ (∀ᵐ x ∂V.weight, x ∈ ball ξ s → V.mult x = 1) ∧ (μHE[n] : Measure (Amb n ℓ)) (symmDiff (V.carrier ∩ ball ξ s) (V.support ∩ ball ξ s)) = 0 ∧ V.weight.restrict (ball ξ s) = (μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ ball ξ s) ∧ (∀ y ∈ ball ξ s ∩ V.support, V.HasDensity y 1) ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ s → (μHE[n] : Measure (Amb n ℓ)) (symmDiff (Q '' ((fun x => x - ξ) '' V.carrier) ∩ ball 0 ρ) (graphOver u {x | x ∈ ball (0 : Rn n) ρ ∧ ‖graphPoint x (u x)‖ < ρ})) = 0`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.c1_graph_density-a1`
- `root.density_one_higher_regularity-a1.graph_tangent_planes-a1`
- `root.density_one_higher_regularity-a1.local_monotonicity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
