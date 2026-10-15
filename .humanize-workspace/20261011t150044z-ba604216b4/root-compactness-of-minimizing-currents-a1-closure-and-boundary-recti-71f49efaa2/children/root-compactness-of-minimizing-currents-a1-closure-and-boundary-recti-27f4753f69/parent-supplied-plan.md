# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.bv_estimate-a1.smooth_test_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-27f4753f69/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.bv_estimate-a1`
- Child key: `smooth_test_bound`
- Declaration: `Submission.cbr_ci_pw_bv_smooth_test_bound`
- Exact Lean type: `∀ (n : ℕ) (R s V : ℝ) (φ u g : Euclid n → ℝ), 0 < R → 0 < s → 2 * s < R → 0 ≤ V → ContDiff ℝ (⊤ : ℕ∞) φ → (∀ y, 0 ≤ φ y) → tsupport φ ⊆ ball 0 s → ∫ y, φ y = 1 → IntegrableOn u (ball 0 (2 * R)) → (∀ (f : Euclid n → ℝ) (z : Euclid n) (M : ℝ), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ ball 0 (2 * R) → (∀ y, |f y| ≤ M) → |∫ y in ball 0 (2 * R), u y * fderiv ℝ f y z| ≤ V * ‖z‖ * M) → ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ ball 0 (R + s) → (∀ x, |g x| ≤ 1) → |∫ x, (u x - ∫ y in ball 0 (2 * R), u y * φ (x - y)) * g x| ≤ s * V`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.bv_estimate-a1.translate_test-a1`
- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.bv_estimate-a1.pairing_identity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
