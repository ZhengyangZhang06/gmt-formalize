# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.dilation_isp-a1.testform_comp-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-bf6ac3d2a2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.dilation_isp-a1`
- Child key: `testform_comp`
- Declaration: `Submission.cbr_ci_dsp_testForm_comp_dilation`
- Exact Lean type: `∀ (P m : ℕ) (a : Euclid P) (lam : ℝ), 0 < lam → ∀ φ : TestFormOn (univ : Set (Euclid P)) m, ∃ φ' : TestFormOn (univ : Set (Euclid P)) m, ∀ y : Euclid P, (φ' : DifferentialForm (Euclid P) m) y = (φ : DifferentialForm (Euclid P) m) (dilation a lam y)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
