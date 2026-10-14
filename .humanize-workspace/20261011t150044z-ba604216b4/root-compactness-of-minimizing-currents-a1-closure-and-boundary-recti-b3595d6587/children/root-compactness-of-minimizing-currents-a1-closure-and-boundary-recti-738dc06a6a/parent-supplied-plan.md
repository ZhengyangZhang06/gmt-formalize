# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.finite_planes-a1.zero_offset-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-738dc06a6a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.finite_planes-a1`
- Child key: `zero_offset`
- Declaration: `Submission.cbr_ci_cp_fp_exists_offset_eq_zero`
- Exact Lean type: `∀ (P n : ℕ) (ν : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)) (N : ℕ) (w : Fin N → Euclid P) (α : Fin N → ℝ), (∀ i, w i ∈ Vᗮ) → ν = ∑ i, ENNReal.ofReal (α i) • (μHE[n]).restrict {y : Euclid P | y - w i ∈ V} → (∀ r : ℝ, 0 < r → 0 < ν (ball 0 r)) → ∃ i, w i = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
