# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.zero_current_sum-a1.finset_integral_h0-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-fe595d3abe/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.zero_current_sum-a1`
- Child key: `finset_integral_h0`
- Declaration: `Submission.cbr_cc_zcs_setIntegral_finset_hausdorff_zero`
- Exact Lean type: `∀ (P : ℕ) (F : Finset (Euclid P)) (f : Euclid P → ℝ), ∫ x in (F : Set (Euclid P)), f x ∂μHE[0] = ∑ x ∈ F, f x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
