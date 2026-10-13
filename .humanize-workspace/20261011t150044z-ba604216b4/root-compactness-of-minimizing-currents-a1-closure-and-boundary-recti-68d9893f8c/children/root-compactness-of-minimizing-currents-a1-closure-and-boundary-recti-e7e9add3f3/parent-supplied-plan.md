# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_zero-a1.count_integral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-e7e9add3f3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_zero-a1`
- Child key: `count_integral`
- Declaration: `Submission.cbrz_finset_integral_hausdorff_zero`
- Exact Lean type: `∀ (P : ℕ) (F : Finset (Euclid P)) (f : Euclid P → ℝ) (g : Euclid P → ℝ≥0∞), (∫ x in (F : Set (Euclid P)), f x ∂μHE[0]) = ∑ x ∈ F, f x ∧ (∫⁻ x in (F : Set (Euclid P)), g x ∂μHE[0]) = ∑ x ∈ F, g x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
