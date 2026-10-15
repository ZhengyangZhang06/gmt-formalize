# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.skeleton_deformation-a1.zero_neg-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-4fc25adda8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.skeleton_deformation-a1`
- Child key: `zero_neg`
- Declaration: `Submission.dor_lmb_fcd_sd_zero_neg`
- Exact Lean type: `∀ (P k : ℕ) (U : Set (Euclid P)), IsOpen U → IsIntegerMultiplicity (0 : GeometricCurrentOn U k) ∧ (∀ X : GeometricCurrentOn U k, IsIntegerMultiplicity X → IsIntegerMultiplicity (0 - X)) ∧ (∀ (X : GeometricCurrentOn U k) (G : Set (Euclid P)), (0 - X).massOn G = X.massOn G) ∧ ∀ (X : GeometricCurrentOn U k) (ω : TestFormOn U k) (s : ℝ), 0 < s → X.mass ≠ ∞ → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ s) → |X ω| ≤ s * X.mass.toReal`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
