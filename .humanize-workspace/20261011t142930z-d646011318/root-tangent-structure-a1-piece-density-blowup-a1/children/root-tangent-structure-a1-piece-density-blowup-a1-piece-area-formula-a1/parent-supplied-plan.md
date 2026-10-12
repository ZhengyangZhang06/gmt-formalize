# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.piece_density_blowup-a1.piece_area_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-density-blowup-a1-piece-area-formula-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.piece_density_blowup-a1`
- Child key: `piece_area_formula`
- Declaration: `Submission.ts_pdb_piece_area_formula`
- Exact Lean type: `∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (K : NNReal), MeasurableSet C → LipschitzWith K F → Set.InjOn F C → ContinuousOn (fderiv ℝ F) C → ∃ J : EuclideanSpace ℝ (Fin n) → ℝ, ContinuousOn J C ∧ (∀ v ∈ C, 0 ≤ J v ∧ ∀ S : Set (EuclideanSpace ℝ (Fin n)), (μHE[n] : Measure (Ambient n ℓ)) (fderiv ℝ F v '' S) = ENNReal.ofReal (J v) * volume S) ∧ ∀ g : Ambient n ℓ → ℝ, Continuous g → ∫ y in F '' C, g y ∂μHE[n] = ∫ v in C, J v * g (F v)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
