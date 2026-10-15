# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1.cylinder_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-9f41123919/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1`
- Child key: `cylinder_tangent`
- Declaration: `Submission.dimred_mbl_dt_lp_imc_cylinder_tangent`
- Exact Lean type: `∀ (N n : ℕ) (M : Set (Euclid N)), MeasurableSet M → CountablyRectifiable n M → μHE[n] M ≠ ∞ → ∀ᵐ y ∂(μHE[n + 1].restrict ((fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) '' (Ioo (0 : ℝ) 1 ×ˢ M))), ∀ (t : ℝ) (x : Euclid N), y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) → ∀ Q : Submodule ℝ (Euclid N), HasApproximateTangentSpaceAt n M x Q → HasApproximateTangentSpaceAt (n + 1) ((fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) '' (Ioo (0 : ℝ) 1 ×ˢ M)) y (Submodule.span ℝ (insert (EuclideanSpace.single 0 1) ((fun v : Euclid N => (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)) : Euclid (N + 1))) '' (Q : Set (Euclid N)))))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1.suspension-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1.product_null-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1.cylinder_measure-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.bilipschitz_pieces-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
