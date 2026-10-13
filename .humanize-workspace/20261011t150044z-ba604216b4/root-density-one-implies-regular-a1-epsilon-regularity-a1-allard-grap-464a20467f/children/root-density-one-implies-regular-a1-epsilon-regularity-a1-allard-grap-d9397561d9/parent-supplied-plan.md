# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1.graph_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-d9397561d9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1`
- Child key: `graph_extension`
- Declaration: `Submission.dorag_lip_cone_set_graph_extension`
- Exact Lean type: `∀ (n k : ℕ) (T₀ : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (ξ : Euclid (n + k)) (G : Set (Euclid (n + k))) (lam A : ℝ), (∀ x, ∃ v w, x = ι v + ι' w) → (∀ v w, T₀.starProjection (ι v + ι' w) = ι v) → 0 ≤ lam → lam ≤ 1 / 2 → 0 ≤ A → (∀ y₁ ∈ G, ∀ y₂ ∈ G, ‖(y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖ ≤ lam * ‖y₂ - y₁‖) → (∀ y ∈ G, ‖(y - ξ) - T₀.starProjection (y - ξ)‖ ≤ A) → ∃ f : Euclid n → Euclid k, (∀ v w, ‖f v - f w‖ ≤ 2 * Real.sqrt k * lam * ‖v - w‖) ∧ (∀ v, ‖f v‖ ≤ Real.sqrt k * A) ∧ G ⊆ range (fun v => ξ + ι v + ι' (f v))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
