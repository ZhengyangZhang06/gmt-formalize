# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.campanato-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-campanato-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1`
- Child key: `campanato`
- Declaration: `Submission.any_radius_campanato`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (r s₀ A α : ℝ), 0 < r → 0 < s₀ → 0 ≤ A → 0 < α → ContinuousOn g (closedBall 0 (r + s₀)) → (∀ᵐ z ∂(volume.restrict (closedBall (0 : Rn n) r)), ∀ s : ℝ, 0 < s → s ≤ s₀ → ∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (g x - g z)) ≤ ENNReal.ofReal (A * s ^ ((n : ℝ) + 2 * α))) → ∀ x ∈ closedBall (0 : Rn n) r, ∀ y ∈ closedBall (0 : Rn n) r, ‖x - y‖ ≤ s₀ / 2 → hsNorm (g x - g y) ≤ Real.sqrt (2 ^ (2 * (n : ℝ) + 2 + 2 * α) * A / unitBallVolume n) * ‖x - y‖ ^ α`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
