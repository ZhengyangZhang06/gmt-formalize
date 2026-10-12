# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.patching-a1.regraph-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1-regraph-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.patching-a1`
- Child key: `regraph`
- Declaration: `Submission.arp_regraph_over_rotatedPlane`
- Exact Lean type: `∀ {n ℓ : ℕ} (q q₀ : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (v : Rn n → Rn ℓ) (y : Amb n ℓ) (c : Rn n) (d : Rn ℓ) (r ε ϑ : ℝ), 0 < r → 0 ≤ ε → ε ≤ 1 / 24 → 0 ≤ ϑ → ϑ ≤ 1 / 12 → ContDiffOn ℝ 1 v (closedBall 0 r) → v 0 = 0 → (∀ x ∈ closedBall (0 : Rn n) r, ‖fderivWithin ℝ v (closedBall 0 r) x‖ ≤ ε) → (∀ x : Rn n, infDist (q (graphPoint x 0)) (rotatedPlane q₀ : Set (Amb n ℓ)) ≤ ϑ * ‖x‖) → y = q₀ (graphPoint c d) → ∃ f : Rn n → Rn ℓ, ContDiffOn ℝ 1 f (ball c (r / 2)) ∧ (∀ w ∈ ball c (r / 2), ‖fderiv ℝ f w‖ ≤ 1 / 7) ∧ (∀ w ∈ closedBall c (r / 2), ∃ x ∈ closedBall (0 : Rn n) r, y + q (graphPoint x (v x)) = q₀ (graphPoint w (f w)) ∧ ‖graphPoint x (v x)‖ ≤ r) ∧ (∀ x ∈ closedBall (0 : Rn n) r, ∀ (w : Rn n) (b : Rn ℓ), y + q (graphPoint x (v x)) = q₀ (graphPoint w b) → w ∈ closedBall c (r / 2) → b = f w)`

## Sibling prerequisites

- `root.allard_any_radius-a1.patching-a1.rotated_coords-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
