# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.vertical_first_variation-a1.rotated_chain_rule-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-vertical-first-varia-ac4a8822a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.vertical_first_variation-a1`
- Child key: `rotated_chain_rule`
- Declaration: `Submission.gwe_vfv_hasFDerivAt_comp_first_block`
- Exact Lean type: `∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (ζ : Rn n → ℝ) (x : Amb n ℓ), DifferentiableAt ℝ ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1 → HasFDerivAt (fun y : Amb n ℓ => ζ (EuclideanSpace.finAddEquivProd (q.symm y)).1) (innerSL ℝ (q (graphPoint (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) 0))) x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
