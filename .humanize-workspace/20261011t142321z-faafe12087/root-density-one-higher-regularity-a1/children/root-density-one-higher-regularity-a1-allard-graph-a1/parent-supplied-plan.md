# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.allard_graph-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-allard-graph-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1`
- Child key: `allard_graph`
- Declaration: `Submission.dohr_allard_graph_at_density_one`
- Exact Lean type: `AllardRegularityTheorem → ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p → V.HasGeneralizedMeanCurvature H → V.LocallyLp H p → (∀ᵐ x ∂V.weight, 1 ≤ V.mult x) → ∀ ξ ∈ U, V.HasDensity ξ 1 → ∃ R > 0, ∃ (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), closedBall ξ R ⊆ U ∧ ContDiffOn ℝ 1 u (ball 0 R) ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧ (∃ K : ℝ, ∀ x ∈ ball (0 : Rn n) R, ∀ y ∈ ball (0 : Rn n) R, ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ K * ‖x - y‖ ^ (1 - (n : ℝ) / p)) ∧ Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.translate_varifold-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
