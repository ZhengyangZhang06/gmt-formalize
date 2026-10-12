# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.first_variation_pieces-a1.variation_bounds-a1.first_order_regularity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-first-variation-pieces-a1-variation-bounds-f9645069b0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.first_variation_pieces-a1.variation_bounds-a1`
- Child key: `first_order_regularity`
- Declaration: `Submission.ts_fv_cv_first_order_regularity`
- Exact Lean type: `∀ (n ℓ : ℕ) (φ : ℝ → Ambient n ℓ → Ambient n ℓ) (ε : ℝ) (K : Set (Ambient n ℓ)), IsCompactVariation φ ε K → ContDiff ℝ 1 (fun y ↦ deriv (fun t ↦ φ t y) 0) ∧ (∀ y ∉ K, fderiv ℝ (fun y ↦ deriv (fun t ↦ φ t y) 0) y = 0) ∧ (∀ t ∈ Ioo (-ε) ε, (∃ L : NNReal, LipschitzWith L (φ t)) ∧ ContDiff ℝ 1 (φ t))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
