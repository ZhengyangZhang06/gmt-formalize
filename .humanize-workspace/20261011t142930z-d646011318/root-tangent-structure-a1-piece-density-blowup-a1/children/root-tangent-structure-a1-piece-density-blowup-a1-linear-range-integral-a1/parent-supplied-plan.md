# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.piece_density_blowup-a1.linear_range_integral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-density-blowup-a1-linear-range-integral-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.piece_density_blowup-a1`
- Child key: `linear_range_integral`
- Declaration: `Submission.ts_pdb_linear_range_integral`
- Exact Lean type: `∀ (n ℓ : ℕ) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) (j : ℝ), 0 ≤ j → (∀ S : Set (EuclideanSpace ℝ (Fin n)), (μHE[n] : Measure (Ambient n ℓ)) (A '' S) = ENNReal.ofReal j * volume S) → ∀ f : C_c(Ambient n ℓ, ℝ), ∫ y in (LinearMap.range A.toLinearMap : Set (Ambient n ℓ)), f y ∂μHE[n] = j * ∫ u, f (A u)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
