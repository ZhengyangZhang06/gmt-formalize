# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.first_variation_mass_bound-a1.gram_jacobian_first_order-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1-g-86ce9f2a61/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.first_variation_mass_bound-a1`
- Child key: `gram_jacobian_first_order`
- Declaration: `Submission.fvmb_orthonormal_gram_sqrt_det_le_first_order`
- Exact Lean type: `∀ (P n : ℕ) (A ε : ℝ), 0 ≤ A → 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ B L : Euclid P →L[ℝ] Euclid P, ‖B‖ ≤ A → ‖L - ContinuousLinearMap.id ℝ (Euclid P) - t • B‖ ≤ η * |t| → ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ → Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (L (τ i)) (L (τ j)))) ≤ 1 + t * ∑ a, inner ℝ (τ a) (B (τ a)) + ε * |t|`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.first_variation_mass_bound-a1.gram_det_exp_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
