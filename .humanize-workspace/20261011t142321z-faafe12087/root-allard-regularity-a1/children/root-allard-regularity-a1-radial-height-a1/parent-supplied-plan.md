# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.radial_height-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-radial-height-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1`
- Child key: `radial_height`
- Declaration: `Submission.allard52_radial_height`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ (α M A : ℝ), 0 < α → α ≤ 1 → 0 ≤ M → 0 ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Rn n → Rn ℓ) (R δ : ℝ), 0 < R → 0 < δ → δ ≤ 1 → f 0 = 0 → ContDiffOn ℝ 1 f (ball 0 R) → LipschitzOnWith 1 f (ball 0 R) → (∀ x ∈ ball (0 : Rn n) R, hsNorm (fderiv ℝ f x) ≤ M * (‖x‖ / R) ^ α) → ∫⁻ x in ball (0 : Rn n) R, ENNReal.ofReal (‖f x - fderiv ℝ f x x‖ ^ 2 / ‖x‖ ^ (n + 2)) ≤ ENNReal.ofReal (A * δ) → ∀ x ∈ ball (0 : Rn n) R, ‖f x‖ ≤ C * δ ^ (1 / (2 * (n : ℝ) + 2)) * ‖x‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
