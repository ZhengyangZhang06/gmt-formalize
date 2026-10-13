# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.translated_varifold-a1.tangent_proj_eq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-translated-varifold-a1-tangent-proj-eq-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.translated_varifold-a1`
- Child key: `tangent_proj_eq`
- Declaration: `Submission.rsod_tv_tangentProj_eq`
- Exact Lean type: `∀ (n ℓ : ℕ) (U U' : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (W : RectifiableVarifold n ℓ U') (x₀ : Amb n ℓ), W.carrier = (fun y => y + x₀) ⁻¹' V.carrier → (∀ y, W.mult y = V.mult (y + x₀)) → ∀ y, W.tangentProj y = V.tangentProj (y + x₀)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
