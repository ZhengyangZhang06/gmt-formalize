# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_plane_algebra-a1.isometry_conj-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-plane-algebra-a1-isometry-conj-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.graph_plane_algebra-a1`
- Child key: `isometry_conj`
- Declaration: `Submission.allard52_gpa_isometry_conj`
- Exact Lean type: `∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), (∀ K : Submodule ℝ (Amb n ℓ), (K.map q.toLinearEquiv.toLinearMap).starProjection = q.toLinearIsometry.toContinuousLinearMap ∘L K.starProjection ∘L q.symm.toLinearIsometry.toContinuousLinearMap) ∧ ∀ X : Amb n ℓ →L[ℝ] Amb n ℓ, hsNormSq (q.toLinearIsometry.toContinuousLinearMap ∘L X ∘L q.symm.toLinearIsometry.toContinuousLinearMap) = hsNormSq X`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
