# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.first_variation_mass_bound-a1.gram_jacobian_first_order-a1.scalar_sqrt_exp_first_order-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1-g-91b8a11902/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.first_variation_mass_bound-a1.gram_jacobian_first_order-a1`
- Child key: `scalar_sqrt_exp_first_order`
- Declaration: `Submission.fvmb_sqrt_le_first_order_of_le_exp`
- Exact Lean type: `∀ (n : ℕ) (A ε : ℝ), 0 ≤ A → 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ t D g : ℝ, |t| < δ → |D| ≤ (n : ℝ) * A → g ≤ Real.exp (2 * t * D + 2 * (n : ℝ) * η * |t| + (n : ℝ) * (A + 1) ^ 2 * t ^ 2) → Real.sqrt g ≤ 1 + t * D + ε * |t|`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
