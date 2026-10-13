# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.segment_current-a1.zero_form_ftc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-a0328cc6d3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.segment_current-a1`
- Child key: `zero_form_ftc`
- Declaration: `Submission.cbr_cc_seg_zero_form_ftc`
- Exact Lean type: `∀ (P : ℕ) (g : DifferentialForm (Euclid P) 0), IsSmoothForm g → ∀ (a v : Euclid P) (ℓ : ℝ), 0 ≤ ℓ → ∫ u in Ioo 0 ℓ, exteriorDerivative g (a + u • v) (fun _ => v) = g (a + ℓ • v) (fun i => i.elim0) - g a (fun i => i.elim0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
