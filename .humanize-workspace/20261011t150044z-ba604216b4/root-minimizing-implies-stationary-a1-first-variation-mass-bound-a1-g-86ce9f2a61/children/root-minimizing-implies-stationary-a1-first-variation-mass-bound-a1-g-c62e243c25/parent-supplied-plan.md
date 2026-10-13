# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.first_variation_mass_bound-a1.gram_jacobian_first_order-a1.perturbed_frame_trace_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1-g-c62e243c25/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.first_variation_mass_bound-a1.gram_jacobian_first_order-a1`
- Child key: `perturbed_frame_trace_bound`
- Declaration: `Submission.fvmb_perturbed_frame_sum_norm_sq_sub_le`
- Exact Lean type: `∀ (P n : ℕ) (A η t : ℝ) (B L : Euclid P →L[ℝ] Euclid P) (τ : Fin n → Euclid P), η ≤ 1 → ‖B‖ ≤ A → ‖L - ContinuousLinearMap.id ℝ (Euclid P) - t • B‖ ≤ η * |t| → Orthonormal ℝ τ → |∑ a, inner ℝ (τ a) (B (τ a))| ≤ (n : ℝ) * A ∧ ∑ a, ‖L (τ a)‖ ^ 2 - (n : ℝ) ≤ 2 * t * (∑ a, inner ℝ (τ a) (B (τ a))) + 2 * (n : ℝ) * η * |t| + (n : ℝ) * (A + 1) ^ 2 * t ^ 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
