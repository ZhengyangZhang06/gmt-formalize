# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.abstract_dimension_reduction-a1.weak_tendsto_comp_affine-a1.integral_comp_affine-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-weak-tendsto-comp-affine-a1-inte-f23f7d3fbf/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.abstract_dimension_reduction-a1.weak_tendsto_comp_affine-a1`
- Child key: `integral_comp_affine`
- Declaration: `Submission.adr_hausdorff_integral_comp_affine`
- Exact Lean type: `∀ (P n Q : ℕ) (h : Euclid P → Euclid Q) (y : Euclid P) (c : ℝ), 0 < c → ∫ x, h (y + c • x) ∂μH[(n : ℝ)] = (c ^ n)⁻¹ • ∫ x, h x ∂μH[(n : ℝ)]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
