# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.top_density-a1.top_covector_spans-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d2a0e8ce99/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.top_density-a1`
- Child key: `top_covector_spans`
- Declaration: `Submission.cbr_ci_pw_td_top_covector_spans`
- Exact Lean type: `∀ (n : ℕ) (δ : Covector (Euclid n) n), δ (fun i => EuclideanSpace.single i (1 : ℝ)) = 1 → covectorEuclideanNorm δ = 1 ∧ ∀ α : Covector (Euclid n) n, α = α (fun i => EuclideanSpace.single i (1 : ℝ)) • δ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
