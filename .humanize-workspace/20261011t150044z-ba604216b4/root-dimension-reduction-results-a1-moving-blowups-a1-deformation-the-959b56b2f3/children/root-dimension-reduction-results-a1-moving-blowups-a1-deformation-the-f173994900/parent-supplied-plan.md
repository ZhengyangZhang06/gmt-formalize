# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1.cylinder_rectifiable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-f173994900/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1`
- Child key: `cylinder_rectifiable`
- Declaration: `Submission.dimred_mbl_dt_lp_imc_cylinder_rectifiable`
- Exact Lean type: `∀ (N n : ℕ) (I : Set ℝ) (M : Set (Euclid N)), CountablyRectifiable n M → CountablyRectifiable (n + 1) ((fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) '' (I ×ˢ M))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1.suspension-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1.product_null-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
