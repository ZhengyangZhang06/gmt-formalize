# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.projection-a1.pullback_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-047ac7dc16/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.projection-a1`
- Child key: `pullback_extension`
- Declaration: `Submission.cbr_ci_pw_proj_pullback_extension`
- Exact Lean type: `∀ (P m l : ℕ) (pL : Euclid P →L[ℝ] Euclid m) (S O : Set (Euclid P)) (γ : DifferentialForm (Euclid m) l), ContDiff ℝ (⊤ : ℕ∞) γ → IsOpen O → IsCompact (S ∩ pL ⁻¹' tsupport γ) → S ∩ pL ⁻¹' tsupport γ ⊆ O → ∃ γ' : TestFormOn (univ : Set (Euclid P)) l, tsupport (γ' : DifferentialForm (Euclid P) l) ⊆ O ∧ (∀ x, covectorEuclideanNorm ((γ' : DifferentialForm (Euclid P) l) x) ≤ covectorEuclideanNorm ((γ (pL x)).compContinuousLinearMap pL)) ∧ (∀ x ∈ S, (γ' : DifferentialForm (Euclid P) l) x = (γ (pL x)).compContinuousLinearMap pL) ∧ ∀ x ∈ S, exteriorDerivative (γ' : DifferentialForm (Euclid P) l) x = (exteriorDerivative γ (pL x)).compContinuousLinearMap pL`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.projection-a1.smooth_cutoff-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
