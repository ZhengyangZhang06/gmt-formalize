# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.patching-a1.global_graph-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1-global-graph-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.patching-a1`
- Child key: `global_graph`
- Declaration: `Submission.arp_global_graph_of_local_graphs`
- Exact Lean type: `∀ {n ℓ : ℕ} (S : Set (Amb n ℓ)) (q₀ : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (R A B s t κ L : ℝ), 0 < R → 0 < s → 0 ≤ κ → κ < 1 → R ≤ (1 - κ) * A → A + t ≤ B → s + 2 * κ * A ≤ t → IsClosed (S ∩ closedBall 0 A) → (0 : Amb n ℓ) ∈ S → (∀ z ∈ S ∩ closedBall 0 B, infDist z (rotatedPlane q₀ : Set (Amb n ℓ)) ≤ κ * ‖z‖) → (∀ y ∈ S ∩ closedBall 0 A, ∀ (c : Rn n) (d : Rn ℓ), y = q₀ (graphPoint c d) → ∃ f : Rn n → Rn ℓ, ContDiffOn ℝ 1 f (ball c s) ∧ (∀ w ∈ ball c s, ‖fderiv ℝ f w‖ ≤ L) ∧ (∀ w ∈ ball c s, q₀ (graphPoint w (f w)) ∈ S ∩ closedBall y t) ∧ (∀ w ∈ ball c s, ∀ b : Rn ℓ, q₀ (graphPoint w b) ∈ S ∩ closedBall y t → b = f w)) → ∃ u : Rn n → Rn ℓ, ContDiffOn ℝ 1 u (ball 0 R) ∧ (∀ x ∈ ball (0 : Rn n) R, ‖fderiv ℝ u x‖ ≤ L) ∧ (∀ x ∈ ball (0 : Rn n) R, q₀ (graphPoint x (u x)) ∈ S ∩ ball 0 A) ∧ (∀ x ∈ ball (0 : Rn n) R, ∀ b : Rn ℓ, q₀ (graphPoint x b) ∈ S ∩ closedBall 0 A → b = u x) ∧ S ∩ ball 0 R ⊆ q₀ '' graphOver u (ball 0 R)`

## Sibling prerequisites

- `root.allard_any_radius-a1.patching-a1.rotated_coords-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
