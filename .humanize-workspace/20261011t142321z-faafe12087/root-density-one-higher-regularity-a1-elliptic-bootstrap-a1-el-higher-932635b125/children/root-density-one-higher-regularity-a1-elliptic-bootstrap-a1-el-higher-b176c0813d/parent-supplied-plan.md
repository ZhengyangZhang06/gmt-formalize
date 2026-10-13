# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1.differentiated_el-a1.test_admissible-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-el-higher-b176c0813d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1.differentiated_el-a1`
- Child key: `test_admissible`
- Declaration: `Submission.dohr_eb_ehs_del_test_admissible`
- Exact Lean type: `∀ n ℓ : ℕ, ∀ (ζ : Rn n → Rn ℓ) (U : Set (Rn n)) (e : Rn n), IsOpen U → ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∀ᶠ h in 𝓝[≠] (0 : ℝ), ContDiff ℝ 1 (fun x => h⁻¹ • (ζ x - ζ (x - h • e))) ∧ HasCompactSupport (fun x => h⁻¹ • (ζ x - ζ (x - h • e))) ∧ tsupport (fun x => h⁻¹ • (ζ x - ζ (x - h • e))) ⊆ U ∧ ∀ y, fderiv ℝ (fun x => h⁻¹ • (ζ x - ζ (x - h • e))) y = h⁻¹ • (fderiv ℝ ζ y - fderiv ℝ ζ (y - h • e))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
