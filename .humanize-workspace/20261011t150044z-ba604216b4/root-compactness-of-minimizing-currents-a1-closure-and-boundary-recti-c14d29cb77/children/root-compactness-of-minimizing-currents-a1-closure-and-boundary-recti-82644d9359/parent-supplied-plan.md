# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1.cutoff_extension-a1.smooth_cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-82644d9359/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1.cutoff_extension-a1`
- Child key: `smooth_cutoff`
- Declaration: `Submission.cbrcs_ce_smooth_cutoff`
- Exact Lean type: `∀ (P : ℕ) (U K : Set (Euclid P)), IsOpen U → IsCompact K → K ⊆ U → ∃ (ζ : Euclid P → ℝ) (N : Set (Euclid P)), ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ U ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ IsOpen N ∧ K ⊆ N ∧ ∀ x ∈ N, ζ x = 1`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
