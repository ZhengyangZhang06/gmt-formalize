# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_jacobian_bounds-a1.gram_symm_psd_trace-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-graph-jacobian-bound-f4497c5a1e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_jacobian_bounds-a1`
- Child key: `gram_symm_psd_trace`
- Declaration: `Submission.gwe_gjb_gram_symm_psd_trace`
- Exact Lean type: `∀ (n ℓ : ℕ) (D : Rn n →L[ℝ] Rn ℓ), Matrix.IsSymm (Matrix.of fun a b : Fin n => inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ)))) ∧ (∀ x : Fin n → ℝ, 0 ≤ dotProduct x (Matrix.mulVec (Matrix.of fun a b : Fin n => inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ)))) x)) ∧ Matrix.trace (Matrix.of fun a b : Fin n => inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ)))) = hsNormSq D`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
