# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.vertical_first_variation-a1.sup_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-vertical-first-varia-f0d91ebdb7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.vertical_first_variation-a1`
- Child key: `sup_bound`
- Declaration: `Submission.gwe_vfv_abs_le_grad_bound_mul_radius`
- Exact Lean type: `∀ n : ℕ, 1 ≤ n → ∀ (ζ : Rn n → ℝ) (r M : ℝ), 0 ≤ r → Differentiable ℝ ζ → tsupport ζ ⊆ ball 0 r → (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ y, |ζ y| ≤ M * r`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
