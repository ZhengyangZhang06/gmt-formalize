# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1.uniform_remainder-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b87e24bae1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1`
- Child key: `uniform_remainder`
- Declaration: `Submission.lpf_c1r_uniform_remainder`
- Exact Lean type: `∀ (n : ℕ) (g : Eucl n → ℝ) (K : ℝ≥0), LipschitzWith K g → ∀ C : Set (Eucl n), IsClosed C → (∀ x ∈ C, DifferentiableAt ℝ g x) → ContinuousOn (fderiv ℝ g) C → ∀ ε : ℝ≥0∞, 0 < ε → ∃ A : Set (Eucl n), IsClosed A ∧ A ⊆ C ∧ (volume : Measure (Eucl n)) (C \ A) < ε ∧ ∀ L : Set (Eucl n), IsCompact L → L ⊆ A → ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ L, ∀ y ∈ A, dist x y < ρ → ‖g y - g x - fderiv ℝ g x (y - x)‖ ≤ δ * ‖y - x‖`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1.egoroff_closed-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
