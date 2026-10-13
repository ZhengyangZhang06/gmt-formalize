# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.jacobian_continuity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-b372f37aac/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1`
- Child key: `jacobian_continuity`
- Declaration: `Submission.dimred_mbl_dt_lp_jacobian_weak_continuity`
- Exact Lean type: `∀ (n N' : ℕ) (L : NNReal) (Hs : ℕ → Euclid n → Euclid N') (H : Euclid n → Euclid N') (w : Euclid n → ℝ) (ω : DifferentialForm (Euclid N') n), (∀ j, LipschitzWith L (Hs j)) → LipschitzWith L H → TendstoUniformly Hs H atTop → Integrable w → Continuous ω → HasCompactSupport ω → Tendsto (fun j => ∫ u, w u * ω (Hs j u) (fun a => fderiv ℝ (Hs j) u (EuclideanSpace.single a 1))) atTop (𝓝 (∫ u, w u * ω (H u) (fun a => fderiv ℝ H u (EuclideanSpace.single a 1))))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
