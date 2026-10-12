# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_regularity-a1.tangent_ae-a1.c1_approximation-a1.uniform_remainder-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-tangent-ae-a1-c1-approximation-a1-unif-fa64b5888c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_regularity-a1.tangent_ae-a1.c1_approximation-a1`
- Child key: `uniform_remainder`
- Declaration: `Submission.tae_c1_uniform_remainder`
- Exact Lean type: `∀ {n : ℕ} (f : Rn n → ℝ) (K : ℝ≥0), LipschitzWith K f → ∀ C : Set (Rn n), IsClosed C → C ⊆ {x | DifferentiableAt ℝ f x} → ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ A : Set (Rn n), A ⊆ C ∧ IsClosed A ∧ volume (C \ A) < δ ∧ ∀ Q : Set (Rn n), IsCompact Q → Q ⊆ A → ∀ η : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ Q, ∀ y ∈ A, dist x y < ρ → ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ η * ‖y - x‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
