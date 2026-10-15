# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_tangent-a1.weighted_blowup_limit-a1.pointwise_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-cb634dcc4c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_tangent-a1.weighted_blowup_limit-a1`
- Child key: `pointwise_limit`
- Declaration: `Submission.dorwbl_weighted_blowup_tendsto_at_point`
- Exact Lean type: `∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k) (G : Euclid n → ℝ) (C : ℝ) (v : Euclid n), (∀ x y, inner ℝ (ι x) (ι' y) = 0) → Continuous f → Measurable G → (∀ u, |G u| ≤ C) → DifferentiableAt ℝ f v → (∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ∫ w in closedBall (0 : Euclid n) R, |G (v + r • w) - G v|) (𝓝[>] 0) (𝓝 0)) → ∀ ψ : Euclid (n + k) → ℝ, Continuous ψ → HasCompactSupport ψ → Tendsto (fun r : ℝ => ∫ w, ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w)) (𝓝[>] 0) (𝓝 (G v * ∫ w, ψ (ι w + ι' (fderiv ℝ f v w))))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_tangent-a1.weighted_blowup_limit-a1.test_integral_vanish-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
