# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.interior_product-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-interio-e2ad70d40d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1`
- Child key: `interior_product`
- Declaration: `Submission.slicing_im_st_interior_product`
- Exact Lean type: `∀ (P m : ℕ) (τ : Fin (m + 1) → Eucl P) (g : Eucl P) (w : NVector (Eucl P) (m + 1)), Orthonormal ℝ τ → g ∈ Submodule.span ℝ (range τ) → g ≠ 0 → (w = simpleNVector τ ∨ w = -simpleNVector τ) → ∃ τ' : Fin m → Eucl P, Orthonormal ℝ τ' ∧ Submodule.span ℝ (range τ') = Submodule.span ℝ (range τ) ⊓ (ℝ ∙ g)ᗮ ∧ (w.comp ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ (‖g‖⁻¹ • g)))) = simpleNVector τ' ∨ w.comp ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ (‖g‖⁻¹ • g)))) = -simpleNVector τ')`

## Sibling prerequisites

- `root.flat_iff_weak-a1.im_series-a1.frame_sign-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
