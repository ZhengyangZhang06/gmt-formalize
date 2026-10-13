# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_graph_corollary-a1.cone_graph_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-cone-graph-extension-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_graph_corollary-a1`
- Child key: `cone_graph_extension`
- Declaration: `Submission.lgc_cone_graph_extension`
- Exact Lean type: `∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (S : Set (Amb n ℓ)) (ε R₀ : ℝ), 0 ≤ ε → ε ≤ 1 / 2 → 0 ≤ R₀ → (∀ y ∈ S, ∀ z ∈ S, infDist (y - z) (rotatedPlane q : Set (Amb n ℓ)) ≤ ε * ‖y - z‖) → (∀ y ∈ S, infDist y (rotatedPlane q : Set (Amb n ℓ)) ≤ R₀) → ∃ f : Rn n → Rn ℓ, LipschitzWith (Real.toNNReal (2 * Real.sqrt ℓ * ε)) f ∧ (∀ x, ‖f x‖ ≤ R₀) ∧ ∀ y ∈ S, ∃ x : Rn n, ‖x‖ ≤ ‖y‖ ∧ q (graphPoint x (f x)) = y`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
