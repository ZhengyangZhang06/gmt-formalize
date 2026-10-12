# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.translated_varifold-a1.locally_lp-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-translated-varifold-a1-locally-lp-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.translated_varifold-a1`
- Child key: `locally_lp`
- Declaration: `Submission.rsod_tv_locallyLp`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (x₀ : Amb n ℓ) (W : RectifiableVarifold n ℓ ((fun y => y + x₀) ⁻¹' U)), W.weight = V.weight.map (fun y => y - x₀) → ∀ (H : Amb n ℓ → Amb n ℓ) (p : ℝ), V.LocallyLp H p → W.LocallyLp (fun y => H (y + x₀)) p`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
