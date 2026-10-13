# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1.isometric_pushforward-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-382dee4359/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1`
- Child key: `isometric_pushforward`
- Declaration: `Submission.dor_lmb_fc_dtop_isometric_pushforward_im`
- Exact Lean type: `∀ (P Q d : ℕ) (L : Euclid P →L[ℝ] Euclid Q) (hL : IsProperMap (fun x => (0 : Euclid Q) + L x)) (T : GeometricCurrentOn (univ : Set (Euclid P)) d), Isometry L → IsIntegerMultiplicity T → IsIntegerMultiplicity (GeometricCurrentOn.affinePushforward (V := (univ : Set (Euclid Q))) L 0 hL T) ∧ (GeometricCurrentOn.affinePushforward (V := (univ : Set (Euclid Q))) L 0 hL T).mass = T.mass`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
