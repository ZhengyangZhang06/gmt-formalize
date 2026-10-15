# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1.cube_stokes-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-264b120214/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1`
- Child key: `cube_stokes`
- Declaration: `Submission.dimred_mbl_dtfrcb_cube_stokes`
- Exact Lean type: `∀ (P m : ℕ) (ι : Fin (m + 1) → Fin P) (b : Fin P → ℤ) (γ : DifferentialForm (Euclid P) m) (G : Euclid (m + 1) → Euclid (m + 1)), ContDiff ℝ 1 G → (∀ (y : Euclid (m + 1)) (i : Fin (m + 1)), G y i = (-1 : ℝ) ^ (i : ℕ) * γ (WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun l => EuclideanSpace.single (ι (Fin.succAbove i l)) (1 : ℝ))) → (∀ y : Euclid (m + 1), exteriorDerivative γ (WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) = LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, exteriorDerivative γ (WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) = ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * ((∫ y in {y : Euclid m | ∀ j, 0 < y j ∧ y j < 1}, γ (WithLp.toLp 2 (fun k => ((b + Pi.single (ι i) 1 : Fin P → ℤ) k : ℝ)) + ∑ j, y j • EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)) (fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ))) - ∫ y in {y : Euclid m | ∀ j, 0 < y j ∧ y j < 1}, γ (WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)) (fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1.cube_partial_ftc-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
