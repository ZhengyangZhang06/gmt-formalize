# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_regularity-a1.tangent_ae-a1.c1_approximation-a1.whitney_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-tangent-ae-a1-c1-approximation-a1-whit-17056b2e48/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_regularity-a1.tangent_ae-a1.c1_approximation-a1`
- Child key: `whitney_extension`
- Declaration: `Submission.tae_whitney_c1_extension`
- Exact Lean type: `∀ {n : ℕ} (A : Set (Rn n)) (h : Rn n → ℝ) (D : Rn n → (Rn n →L[ℝ] ℝ)), IsClosed A → ContinuousOn h A → ContinuousOn D A → (∀ Q : Set (Rn n), IsCompact Q → Q ⊆ A → ∀ η : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ Q, ∀ y ∈ A, dist x y < ρ → ‖h y - h x - D x (y - x)‖ ≤ η * ‖y - x‖) → ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧ (∀ a ∈ A, g a = h a) ∧ ∀ a ∈ A, HasFDerivAt g (D a) a`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
