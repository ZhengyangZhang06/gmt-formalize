# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.vertical_first_variation-a1.rank_one_divergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-vertical-first-varia-ecc602208d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.vertical_first_variation-a1`
- Child key: `rank_one_divergence`
- Declaration: `Submission.gwe_vfv_divM_smul_const_eq_inner`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (f : Amb n ℓ → ℝ) (e g x : Amb n ℓ), HasFDerivAt f (innerSL ℝ g) x → V.divM (fun y => f y • e) x = inner ℝ (V.tangentProj x e) (V.tangentProj x g)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
