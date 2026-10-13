# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.dq_uniform_bounds-a1.wd_props-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-linear-hi-9019aa5ff6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.dq_uniform_bounds-a1`
- Child key: `wd_props`
- Declaration: `Submission.dohr_eb_lhr_dqub_wd_props`
- Exact Lean type: `∀ (n ℓ : ℕ) (α : ℝ) (U : Set (Rn n)) (v : Rn n → Rn ℓ) (xb e : Rn n) (R : ℝ), IsOpen U → 0 < R → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → IsLocallyHolderCkα 1 α v U → ∃ S : ℝ, ∀ d : ℝ, d ≠ 0 → |d| < R → (∀ x ∈ ball xb (2 * R), ‖d⁻¹ • (v (x + d • e) - v x)‖ ≤ S) ∧ ContDiffOn ℝ 1 (fun z => d⁻¹ • (v (z + d • e) - v z)) (ball xb (2 * R)) ∧ (∀ x ∈ ball xb (2 * R), fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x = d⁻¹ • (fderiv ℝ v (x + d • e) - fderiv ℝ v x)) ∧ ∃ K : ℝ, ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ‖fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x - fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) y‖ ≤ K * ‖x - y‖ ^ α`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.dq_uniform_bounds-a1.fderiv_consts-a1`
- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.dq_uniform_bounds-a1.dq_mean_value-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
