# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.rectifiable_c1_cover-a1.c1_approx_ball-a1.uniform_taylor_remainder-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-rectifiable-c1-cover-a1-c1-approx-ball-b52c4c1082/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.rectifiable_c1_cover-a1.c1_approx_ball-a1`
- Child key: `uniform_taylor_remainder`
- Declaration: `Submission.rsod_c1ab_uniform_taylor_remainder`
- Exact Lean type: `∀ (n : ℕ) (f : Rn n → ℝ) (K : ℝ≥0), LipschitzWith K f → ∀ C : Set (Rn n), IsClosed C → volume C ≠ ∞ → (∀ x ∈ C, DifferentiableAt ℝ f x) → ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ A : Set (Rn n), A ⊆ C ∧ IsClosed A ∧ volume (C \ A) < δ ∧ ∀ τ : ℝ, 0 < τ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ A, ∀ y ∈ A, dist x y < ρ → ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ τ * ‖y - x‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
