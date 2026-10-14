# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1.minor_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-85d5c4f3c5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1`
- Child key: `minor_bound`
- Declaration: `Submission.dor_lmb_fcd_jwc_minor_measurable_bound`
- Exact Lean type: `∀ (k r : ℕ) (L : NNReal) (g : Fin r → Euclid k → ℝ) (V : Fin r → Euclid k), (∀ c, LipschitzWith L (g c)) → Measurable (fun x => Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b))) ∧ ∀ x, |Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b))| ≤ (r.factorial : ℝ) * ((L : ℝ) * ∑ b, ‖V b‖) ^ r`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
