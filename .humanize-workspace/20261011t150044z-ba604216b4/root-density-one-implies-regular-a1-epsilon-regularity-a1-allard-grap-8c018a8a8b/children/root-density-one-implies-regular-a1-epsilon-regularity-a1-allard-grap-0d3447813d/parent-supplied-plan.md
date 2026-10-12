# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_tangent-a1.weighted_blowup_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-0d3447813d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_tangent-a1`
- Child key: `weighted_blowup_limit`
- Declaration: `Submission.doraggt_ae_weighted_graph_blowup_tendsto`
- Exact Lean type: `∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k) (L : NNReal) (G : Euclid n → ℝ) (C : ℝ), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → LipschitzWith L f → Measurable G → (∀ u, |G u| ≤ C) → ∀ᵐ v ∂(volume : Measure (Euclid n)), DifferentiableAt ℝ f v ∧ ∀ ψ : Euclid (n + k) → ℝ, Continuous ψ → HasCompactSupport ψ → Tendsto (fun r : ℝ => ∫ w, ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w)) (𝓝[>] 0) (𝓝 (G v * ∫ w, ψ (ι w + ι' (fderiv ℝ f v w))))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_tangent-a1.lebesgue_rescaled-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
