# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.c1_parametric_coarea-a1.flat_jacobian-a1.section_normdet-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-c1-parametric-coarea-a1-flat-jacobian-a1-se-694cb2d974/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1.flat_jacobian-a1`
- Child key: `section_normdet`
- Declaration: `Submission.pcoarea_flat_normDet_section`
- Exact Lean type: `∀ (n k N : ℕ) (A : Rn n →ₗ[ℝ] Rn N) (K : Submodule ℝ (Rn n)) (S : Rn n →ₗ[ℝ] Rn k) (E : Rn k →ₗ[ℝ] Rn n), Module.finrank ℝ K = k → (∀ z, E z ∈ K) → (∀ z, S (E z) = z) → (A ∘ₗ E).normDet * (S ∘ₗ K.subtype).normDet = (A ∘ₗ K.subtype).normDet`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
