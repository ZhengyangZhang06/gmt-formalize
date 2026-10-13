# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.density_bounds-a1.weight_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-4299718967/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.density_bounds-a1`
- Child key: `weight_bound`
- Declaration: `Submission.cbr_ci_bl_db_weight_le_enorm`
- Exact Lean type: `∀ (P n : ℕ) (ζx ζa : MultiVector P n) (t t₀ C : ℝ), 0 ≤ t₀ → 0 ≤ C → (∀ α : Covector (Euclid P) n, ‖α‖ ≤ C * covectorEuclideanNorm α) → (∀ α : Covector (Euclid P) n, |ζa α| ≤ covectorEuclideanNorm α) → (∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ζx β = 1) → ENNReal.ofReal t ≤ ENNReal.ofReal t₀ + ENNReal.ofReal C * ‖t • ζx - t₀ • ζa‖ₑ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
