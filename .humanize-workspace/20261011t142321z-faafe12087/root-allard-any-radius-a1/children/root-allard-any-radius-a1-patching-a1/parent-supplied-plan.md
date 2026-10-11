# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.patching-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1`
- Child key: `patching`
- Declaration: `Submission.any_radius_patching`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ (S : Set (Amb n ℓ)) (ρ γh γa γb r ε κ r₀ : ℝ) (q₀ : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u₀ : Rn n → Rn ℓ), 0 < ρ → 0 < γh → γh < γa → 0 < r → γa * ρ + r ≤ γb * ρ → γb ≤ 1 → 0 ≤ ε → ε ≤ 1 / 24 → 0 < κ → 48 * κ * ρ ≤ r → γh ≤ (1 - κ) * γa → 0 < r₀ → r₀ ≤ γh * ρ → IsClosed (S ∩ closedBall 0 ρ) → (∀ y ∈ S ∩ closedBall 0 (γa * ρ), ∃ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (v : Rn n → Rn ℓ), ContDiffOn ℝ 1 v (closedBall 0 r) ∧ v 0 = 0 ∧ (∀ x ∈ closedBall (0 : Rn n) r, hsNorm (fderivWithin ℝ v (closedBall 0 r) x) ≤ ε) ∧ (fun x => y + x) ⁻¹' S ∩ closedBall 0 r = q '' graphOver v (closedBall 0 r) ∩ closedBall 0 r) → (∀ y ∈ S ∩ closedBall 0 (γb * ρ), infDist y (rotatedPlane q₀ : Set (Amb n ℓ)) ≤ κ * ‖y‖) → ContDiffOn ℝ 1 u₀ (closedBall 0 r₀) → u₀ 0 = 0 → fderivWithin ℝ u₀ (closedBall 0 r₀) 0 = 0 → (∀ x ∈ closedBall (0 : Rn n) r₀, ‖fderivWithin ℝ u₀ (closedBall 0 r₀) x‖ ≤ 1) → S ∩ closedBall 0 r₀ = q₀ '' graphOver u₀ (closedBall 0 r₀) ∩ closedBall 0 r₀ → ∃ u : Rn n → Rn ℓ, ContDiffOn ℝ 1 u (ball 0 (γh * ρ)) ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧ (∀ x ∈ ball (0 : Rn n) (γh * ρ), ‖fderiv ℝ u x‖ ≤ 1 / 7) ∧ (∀ x ∈ ball (0 : Rn n) (r₀ / 2), u x = u₀ x) ∧ q₀ '' graphOver u (ball 0 (γh * ρ)) ⊆ S ∩ ball 0 (γa * ρ) ∧ S ∩ ball 0 (γh * ρ) ⊆ q₀ '' graphOver u (ball 0 (γh * ρ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
