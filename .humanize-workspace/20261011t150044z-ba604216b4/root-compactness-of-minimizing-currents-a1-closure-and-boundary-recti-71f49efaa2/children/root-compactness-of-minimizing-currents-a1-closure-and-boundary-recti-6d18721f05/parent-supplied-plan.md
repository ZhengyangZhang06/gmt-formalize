# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.bv_estimate-a1.translate_test-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6d18721f05/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.bv_estimate-a1`
- Child key: `translate_test`
- Declaration: `Submission.cbr_ci_pw_bv_translate_test`
- Exact Lean type: `∀ (n : ℕ) (ρ V M : ℝ) (u g : Euclid n → ℝ) (v : Euclid n), IntegrableOn u (ball 0 ρ) → (∀ (f : Euclid n → ℝ) (z : Euclid n) (K : ℝ), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ ball 0 ρ → (∀ y, |f y| ≤ K) → |∫ y in ball 0 ρ, u y * fderiv ℝ f y z| ≤ V * ‖z‖ * K) → ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ ball 0 (ρ - ‖v‖) → (∀ y, |g y| ≤ M) → |∫ y in ball 0 ρ, u y * (g (y + v) - g y)| ≤ V * ‖v‖ * M`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
