# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.patching-a1.tilt_of_slab-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1-tilt-of-slab-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.patching-a1`
- Child key: `tilt_of_slab`
- Declaration: `Submission.arp_tilt_le_of_slab`
- Exact Lean type: `∀ {n ℓ : ℕ} (q q₀ : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (v : Rn n → Rn ℓ) (y : Amb n ℓ) (s ε h : ℝ), 0 < s → (∀ x₁ ∈ closedBall (0 : Rn n) s, ∀ x₂ ∈ closedBall (0 : Rn n) s, ‖v x₁ - v x₂‖ ≤ ε * ‖x₁ - x₂‖) → (∀ x ∈ closedBall (0 : Rn n) s, infDist (y + q (graphPoint x (v x))) (rotatedPlane q₀ : Set (Amb n ℓ)) ≤ h) → ∀ e : Rn n, infDist (q (graphPoint e 0)) (rotatedPlane q₀ : Set (Amb n ℓ)) ≤ (h / s + ε) * ‖e‖`

## Sibling prerequisites

- `root.allard_any_radius-a1.patching-a1.rotated_coords-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
