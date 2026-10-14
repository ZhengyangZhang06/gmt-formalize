# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1.cube_stokes-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-8758ac034a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1`
- Child key: `cube_stokes`
- Declaration: `Submission.cmcdtfrcb_cube_stokes`
- Exact Lean type: `∀ (P m : ℕ) (ι : Fin (m + 1) → Fin P) (b : Fin P → ℤ) (γ : DifferentialForm (Euclid P) m), ContDiff ℝ 1 γ → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, exteriorDerivative γ (WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) = ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * ((∫ y in {y : Euclid m | ∀ j, 0 < y j ∧ y j < 1}, γ (WithLp.toLp 2 (fun k => ((b + Pi.single (ι i) 1 : Fin P → ℤ) k : ℝ)) + ∑ j, y j • EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)) (fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ))) - ∫ y in {y : Euclid m | ∀ j, 0 < y j ∧ y j < 1}, γ (WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)) (fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)))`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1.cube_partial_ftc-a1`
- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1.pullback_divergence-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
