# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1.piola_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-d7f6de7d4c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1`
- Child key: `piola_identity`
- Declaration: `Submission.dor_lmb_fcd_jwc_piola_identity`
- Exact Lean type: `∀ (k r : ℕ) (g : Fin r → Euclid k → ℝ) (V : Fin (r + 1) → Euclid k) (x : Euclid k), (∀ c, ContDiff ℝ 2 (g c)) → ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (fun y => Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c) y (V (b.succAbove b')))) x (V b) = 0`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.mass_representation-a1.coordinate_covectors-a1.det_covector_exists-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
