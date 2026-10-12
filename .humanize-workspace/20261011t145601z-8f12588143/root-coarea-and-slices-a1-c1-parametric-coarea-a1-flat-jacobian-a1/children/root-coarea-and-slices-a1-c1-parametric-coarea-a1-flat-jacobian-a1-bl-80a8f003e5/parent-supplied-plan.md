# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.c1_parametric_coarea-a1.flat_jacobian-a1.block_normdet-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-c1-parametric-coarea-a1-flat-jacobian-a1-bl-80a8f003e5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1.flat_jacobian-a1`
- Child key: `block_normdet`
- Declaration: `Submission.pcoarea_flat_normDet_block`
- Exact Lean type: `∀ (m k : ℕ) (Γ : Rn (m + k) →ₗ[ℝ] Rn m) (S : Rn (m + k) →ₗ[ℝ] Rn k) (T : Rn (m + k) →ₗ[ℝ] WithLp 2 (Rn m × Rn k)), Function.Surjective Γ → (∀ v, (T v).fst = Γ v) → (∀ v, (T v).snd = S v) → T.normDet = (Γ.domRestrict (LinearMap.ker Γ)ᗮ).normDet * (S ∘ₗ (LinearMap.ker Γ).subtype).normDet`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
