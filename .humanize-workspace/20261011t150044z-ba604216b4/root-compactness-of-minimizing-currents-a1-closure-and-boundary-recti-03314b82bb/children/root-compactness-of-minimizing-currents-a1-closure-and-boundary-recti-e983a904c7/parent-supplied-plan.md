# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.mollified_uniform-a1.conv_lipschitz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-e983a904c7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.mollified_uniform-a1`
- Child key: `conv_lipschitz`
- Declaration: `Submission.cbr_ci_pw_mu_conv_lipschitz`
- Exact Lean type: `∀ (n : ℕ) (φ : Euclid n → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∃ L : ℝ, 0 ≤ L ∧ ∀ (S : Set (Euclid n)) (v : Euclid n → ℝ), IntegrableOn v S → ∀ x x' : Euclid n, |(∫ y in S, v y * φ (x - y)) - ∫ y in S, v y * φ (x' - y)| ≤ L * (∫ y in S, |v y|) * dist x x'`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
