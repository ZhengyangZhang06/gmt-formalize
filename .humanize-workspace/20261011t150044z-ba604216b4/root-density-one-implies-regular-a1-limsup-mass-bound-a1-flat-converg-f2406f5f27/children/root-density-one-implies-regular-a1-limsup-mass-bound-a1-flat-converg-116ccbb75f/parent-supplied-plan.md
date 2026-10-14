# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.skeleton_deformation-a1.markov_point-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-116ccbb75f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.skeleton_deformation-a1`
- Child key: `markov_point`
- Declaration: `Submission.dor_lmb_fcd_sd_markov_point`
- Exact Lean type: `∀ (g : ℝ → ℝ≥0∞) (p : ℝ → Prop) (a b : ℝ) (I : ℝ≥0∞), a < b → AEMeasurable g → (∀ᵐ t, p t) → ∫⁻ t in Ioo a b, g t ≤ I → ∃ t ∈ Ioo a b, p t ∧ ENNReal.ofReal (b - a) * g t ≤ 2 * I`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
