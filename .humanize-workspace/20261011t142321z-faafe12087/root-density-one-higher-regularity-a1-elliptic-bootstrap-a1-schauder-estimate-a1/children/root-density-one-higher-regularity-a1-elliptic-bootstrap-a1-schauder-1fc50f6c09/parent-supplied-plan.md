# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.zero_mean-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-1fc50f6c09/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1`
- Child key: `zero_mean`
- Declaration: `Submission.dohr_eb_sch_integral_clm_fderiv_eq_zero`
- Exact Lean type: `∀ (n ℓ : ℕ) (c : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (ζ : Rn n → Rn ℓ), ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, c (fderiv ℝ ζ x) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
