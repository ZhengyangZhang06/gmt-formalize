# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_jacobian_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-graph-jacobian-bounds-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1`
- Child key: `graph_jacobian_bounds`
- Declaration: `Submission.gwe_graph_jacobian_bounds`
- Exact Lean type: `∀ (n ℓ : ℕ) (D : Rn n →L[ℝ] Rn ℓ), 1 ≤ Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ))))) ∧ (‖D‖ ≤ 1 → Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ))))) ≤ 1 + Real.exp ((n : ℝ) / 2) / 2 * hsNormSq D)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
