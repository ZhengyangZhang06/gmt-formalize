# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.liouville-a1.dir_deriv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-1d68d74191/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.liouville-a1`
- Child key: `dir_deriv`
- Declaration: `Submission.dohr_eb_sch_liou_dir_deriv_solution`
- Exact Lean type: `∀ (n ℓ : ℕ) (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (V : Rn n → Rn ℓ) (v : Rn n), ContDiff ℝ 2 V → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) = 0) → ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, A (fderiv ℝ (fun y => fderiv ℝ V y v) x) (fderiv ℝ ζ x) = 0`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.liouville-a1.snd_deriv_symm-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
