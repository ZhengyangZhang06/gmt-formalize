# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.mollified_uniform-a1.translate_admissible-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-f3f172da4a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.mollified_uniform-a1`
- Child key: `translate_admissible`
- Declaration: `Submission.cbr_ci_pw_mu_translate_admissible`
- Exact Lean type: `∀ (n : ℕ) (R s : ℝ) (φ : Euclid n → ℝ) (x : Euclid n), s < R → ContDiff ℝ (⊤ : ℕ∞) φ → tsupport φ ⊆ ball 0 s → x ∈ closedBall 0 R → ContDiff ℝ (⊤ : ℕ∞) (fun y => φ (x - y)) ∧ HasCompactSupport (fun y => φ (x - y)) ∧ tsupport (fun y => φ (x - y)) ⊆ ball 0 (2 * R) ∧ ∫ y, φ (x - y) = ∫ y, φ y`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
