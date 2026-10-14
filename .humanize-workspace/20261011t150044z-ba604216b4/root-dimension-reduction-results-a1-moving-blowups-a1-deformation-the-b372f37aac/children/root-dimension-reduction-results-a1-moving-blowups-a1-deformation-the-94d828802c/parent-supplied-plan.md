# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.jacobian_continuity-a1.lipschitz_minor_ibp-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-94d828802c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.jacobian_continuity-a1`
- Child key: `lipschitz_minor_ibp`
- Declaration: `Submission.dimred_mbl_dt_lp_jc_lipschitz_minor_ibp`
- Exact Lean type: `∀ (k r : ℕ) (L : NNReal) (g : Fin (r + 1) → Euclid k → ℝ) (V : Fin (r + 1) → Euclid k) (ψ : Euclid k → ℝ), (∀ c, LipschitzWith L (g c)) → ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∫ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)) = -∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * ∫ x, fderiv ℝ ψ x (V b) * g 0 x * Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c.succ) x (V (b.succAbove b')))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1.minor_bound-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.jacobian_continuity-a1.lipschitz_smooth_approx-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.jacobian_continuity-a1.smooth_minor_ibp-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
