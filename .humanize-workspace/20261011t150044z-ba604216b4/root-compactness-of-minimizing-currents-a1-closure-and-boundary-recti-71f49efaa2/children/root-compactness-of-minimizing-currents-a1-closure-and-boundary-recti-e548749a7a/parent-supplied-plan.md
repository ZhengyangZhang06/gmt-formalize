# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.bv_estimate-a1.pairing_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-e548749a7a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.bv_estimate-a1`
- Child key: `pairing_identity`
- Declaration: `Submission.cbr_ci_pw_bv_pairing_identity`
- Exact Lean type: `∀ (n : ℕ) (S : Set (Euclid n)) (φ u g : Euclid n → ℝ), MeasurableSet S → Continuous φ → HasCompactSupport φ → ∫ y, φ y = 1 → IntegrableOn u S → Continuous g → HasCompactSupport g → (∀ x, x ∉ S → g x = 0) → ∫ x, (u x - ∫ y in S, u y * φ (x - y)) * g x = ∫ z, φ z * ∫ y in S, u y * (g y - g (y + z))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
