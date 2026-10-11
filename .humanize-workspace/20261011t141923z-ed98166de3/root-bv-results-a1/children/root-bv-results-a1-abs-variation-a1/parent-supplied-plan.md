# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.bv_results-a1.abs_variation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-abs-variation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.bv_results-a1`
- Child key: `abs_variation`
- Declaration: `Submission.bv_abs_variation_le`
- Exact Lean type: `∀ (n : ℕ) (O : Set (Rn n)) (u : Rn n → ℝ), IsOpen O → LocallyIntegrableOn u O volume → Chapter02.bvVariationOn (fun x ↦ |u x|) O ≤ Chapter02.bvVariationOn u O`

## Sibling prerequisites

- `root.bv_results-a1.lipschitz_ibp-a1`
- `root.bv_results-a1.mollifier_l1-a1`
- `root.bv_results-a1.mollifier_gradient-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
