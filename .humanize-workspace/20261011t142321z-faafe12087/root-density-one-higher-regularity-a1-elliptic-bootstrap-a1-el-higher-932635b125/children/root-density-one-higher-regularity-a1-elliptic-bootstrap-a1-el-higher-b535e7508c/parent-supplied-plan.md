# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1.differentiated_el-a1.rhs_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-el-higher-b535e7508c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1.differentiated_el-a1`
- Child key: `rhs_limit`
- Declaration: `Submission.dohr_eb_ehs_del_rhs_tendsto`
- Exact Lean type: `∀ n ℓ : ℕ, ∀ (ζ g : Rn n → Rn ℓ) (U : Set (Rn n)) (e : Rn n), IsOpen U → ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ContinuousOn g U → Tendsto (fun h : ℝ => ∫ x in U, inner ℝ (h⁻¹ • (ζ x - ζ (x - h • e))) (g x)) (𝓝[≠] 0) (𝓝 (∫ x in U, inner ℝ (fderiv ℝ ζ x e) (g x)))`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1.differentiated_el-a1.diffquot_uniform-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
