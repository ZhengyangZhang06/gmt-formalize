# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1.cube_partial_ftc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-bc5e28eaea/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1`
- Child key: `cube_partial_ftc`
- Declaration: `Submission.cmcdtfrcb_cube_partial_ftc`
- Exact Lean type: `∀ (k : ℕ) (i : Fin (k + 1)) (G : Euclid (k + 1) → ℝ), ContDiff ℝ 1 G → IntegrableOn (fun y => fderiv ℝ G y (EuclideanSpace.single i (1 : ℝ))) {y : Euclid (k + 1) | ∀ j, 0 < y j ∧ y j < 1} ∧ ∫ y in {y : Euclid (k + 1) | ∀ j, 0 < y j ∧ y j < 1}, fderiv ℝ G y (EuclideanSpace.single i (1 : ℝ)) = (∫ y in {y : Euclid k | ∀ j, 0 < y j ∧ y j < 1}, G (WithLp.toLp 2 (Fin.insertNth i (1 : ℝ) (WithLp.ofLp y)))) - ∫ y in {y : Euclid k | ∀ j, 0 < y j ∧ y j < 1}, G (WithLp.toLp 2 (Fin.insertNth i (0 : ℝ) (WithLp.ofLp y)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
