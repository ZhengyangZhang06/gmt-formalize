# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1.cutoff_pullback-a1.cutoff_converges-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-4fbf6e3d89/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1.cutoff_pullback-a1`
- Child key: `cutoff_converges`
- Declaration: `Submission.dor_lmb_fc_dtop_cp_cutoff_pullback_converges`
- Exact Lean type: `∀ (P Q d : ℕ) (L : Euclid Q →L[ℝ] Euclid P) (ζ : Euclid Q → ℝ), ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → ∀ (ωs : ℕ → TestFormOn (univ : Set (Euclid P)) d) (ηs : ℕ → TestFormOn (univ : Set (Euclid Q)) d), (∀ (j : ℕ) (y : Euclid Q), (ηs j : DifferentialForm (Euclid Q) d) y = ζ y • ((ωs j : DifferentialForm (Euclid P) d) (L y)).compContinuousLinearMap L) → TestFormOnConverges ωs 0 → TestFormOnConverges ηs 0`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1.cutoff_pullback-a1.leibniz_smul-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
