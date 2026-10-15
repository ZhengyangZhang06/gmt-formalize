# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1.coordinate_covectors-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-a89d08b02c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1`
- Child key: `coordinate_covectors`
- Declaration: `Submission.dor_lmb_fcd_fr_coordinate_covectors`
- Exact Lean type: `∀ (P k : ℕ), ∃ dx : (Fin k → Fin P) → Covector (Euclid P) k, (∀ I J : Fin k → Fin P, StrictMono I → StrictMono J → dx J (fun r => EuclideanSpace.single (I r) (1 : ℝ)) = if I = J then 1 else 0) ∧ ∀ (N : ℕ) (J : Fin N → Fin k → Fin P) (c : Fin N → ℝ), Function.Injective J → (∀ l, StrictMono (J l)) → covectorEuclideanNorm (∑ l, c l • dx (J l)) = Real.sqrt (∑ l, c l ^ 2)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
