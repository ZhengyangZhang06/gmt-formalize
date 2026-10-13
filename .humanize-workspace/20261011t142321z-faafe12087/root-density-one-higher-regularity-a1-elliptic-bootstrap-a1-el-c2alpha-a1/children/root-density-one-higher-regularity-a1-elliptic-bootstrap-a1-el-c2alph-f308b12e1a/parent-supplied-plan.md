# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1.dq_basic-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-el-c2alph-f308b12e1a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1`
- Child key: `dq_basic`
- Declaration: `Submission.dohr_eb_elc2_dq_basic`
- Exact Lean type: `∀ (n ℓ : ℕ) (u : Rn n → Rn ℓ) (U V K : Set (Rn n)) (e : Rn n) (d ε H α : ℝ), IsOpen U → ContDiffOn ℝ 1 u U → K ⊆ U → d ≠ 0 → (∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, x + (t * d) • e ∈ K) → (∀ x ∈ K, ‖fderiv ℝ u x‖ ≤ ε) → (∀ x ∈ K, ∀ y ∈ K, ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ H * ‖x - y‖ ^ α) → ContDiffOn ℝ 1 (fun z => d⁻¹ • (u (z + d • e) - u z)) V ∧ (∀ x ∈ V, fderiv ℝ (fun z => d⁻¹ • (u (z + d • e) - u z)) x = d⁻¹ • (fderiv ℝ u (x + d • e) - fderiv ℝ u x)) ∧ (∀ x ∈ V, ‖d⁻¹ • (u (x + d • e) - u x)‖ ≤ ε * ‖e‖) ∧ ∀ x ∈ V, ∀ y ∈ V, ‖fderiv ℝ (fun z => d⁻¹ • (u (z + d • e) - u z)) x - fderiv ℝ (fun z => d⁻¹ • (u (z + d • e) - u z)) y‖ ≤ 2 * |d|⁻¹ * H * ‖x - y‖ ^ α`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
