# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_current-a1.imrep_vanish_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-29431f4c74/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_current-a1`
- Child key: `imrep_vanish_bound`
- Declaration: `Submission.dimred_cs_sos_cfs_cc_imrep_vanish_bound`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U n) (R : IMRep U n), R.Represents X → (∀ γ : TestFormOn U n, (∀ x ∈ R.carrier, (γ : DifferentialForm (Euclid P) n) x = 0) → X γ = 0) ∧ (R.measure univ ≠ ∞ → ∀ (γ : TestFormOn U n) (b : ℝ), (∀ x, ‖(γ : DifferentialForm (Euclid P) n) x‖ ≤ b) → |X γ| ≤ (R.measure univ).toReal * b)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
