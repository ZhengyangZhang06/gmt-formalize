# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.radial_height-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-radial-height-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1`
- Child key: `radial_height`
- Declaration: `Submission.any_radius_radial_height`
- Exact Lean type: `∀ (n : ℕ), 1 ≤ n → ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℕ) (u : Rn n → Rn ℓ) (R r₁ ε m : ℝ), 0 < r₁ → r₁ < R → 0 ≤ ε → 0 ≤ m → ContDiffOn ℝ 1 u (ball 0 R) → u 0 = 0 → (∀ x ∈ ball (0 : Rn n) R, ‖fderiv ℝ u x‖ ≤ 1) → (∀ x ∈ ball (0 : Rn n) r₁, ‖u x‖ ≤ ε * ‖x‖) → ∫⁻ x in ball (0 : Rn n) R, ENNReal.ofReal (‖u x - fderiv ℝ u x x‖ ^ 2 / ‖x‖ ^ (n + 2)) ≤ ENNReal.ofReal m → ∀ x ∈ ball (0 : Rn n) R, ‖u x‖ ≤ (ε + C * (Real.log (R / r₁) * m) ^ (1 / ((n : ℝ) + 1))) * ‖x‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
