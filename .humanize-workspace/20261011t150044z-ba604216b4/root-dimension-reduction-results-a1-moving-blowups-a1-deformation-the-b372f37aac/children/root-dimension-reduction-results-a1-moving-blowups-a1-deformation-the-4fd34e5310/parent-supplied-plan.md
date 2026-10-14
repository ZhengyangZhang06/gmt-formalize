# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.jacobian_continuity-a1.minor_weak_continuity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-4fd34e5310/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.jacobian_continuity-a1`
- Child key: `minor_weak_continuity`
- Declaration: `Submission.dimred_mbl_dt_lp_jc_minor_weak_continuity`
- Exact Lean type: `∀ (k r : ℕ) (L : NNReal) (gs : ℕ → Fin r → Euclid k → ℝ) (g : Fin r → Euclid k → ℝ) (V : Fin r → Euclid k) (φ : Euclid k → ℝ), Integrable φ → (∀ j c, LipschitzWith L (gs j c)) → (∀ c, LipschitzWith L (g c)) → (∀ c, TendstoUniformly (fun j => gs j c) (g c) atTop) → Tendsto (fun j => ∫ x, φ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (gs j c) x (V b))) atTop (𝓝 (∫ x, φ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b))))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1.minor_bound-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.jacobian_continuity-a1.lipschitz_minor_ibp-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1.weak_star_l1_upgrade-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
