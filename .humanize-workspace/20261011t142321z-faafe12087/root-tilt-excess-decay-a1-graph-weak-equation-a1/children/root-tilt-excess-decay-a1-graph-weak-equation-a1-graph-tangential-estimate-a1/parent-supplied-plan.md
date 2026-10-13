# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tangential_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-graph-tangential-estimate-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1`
- Child key: `graph_tangential_estimate`
- Declaration: `Submission.gwe_graph_tangential_estimate`
- Exact Lean type: `∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → AEStronglyMeasurable V.tangentProj V.weight → ∀ σ : ℝ, 0 < σ → closedBall 0 σ ⊆ U → ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ), LipschitzOnWith 1 f (closedBall 0 (σ / 2)) → (∀ x ∈ closedBall (0 : Rn n) (σ / 2), ‖f x‖ ≤ σ / 16) → (∀ x ∈ V.support ∩ closedBall 0 σ, infDist x (rotatedPlane q : Set (Amb n ℓ)) ≤ σ / 16) → (∀ᵐ x ∂V.weight, ∀ x' ∈ ball (0 : Rn n) (σ / 2), x = q (graphPoint x' (f x')) → DifferentiableAt ℝ f x' → V.tangentProj x = (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (fderiv ℝ f x' v)))).starProjection) → ∀ ζ : Rn n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 (σ / 4) → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ j : Fin ℓ, |∫ x in q '' graphOver f (ball 0 (σ / 4)), inner ℝ (gradient (fun y => f y j) (EuclideanSpace.finAddEquivProd (q.symm x)).1) (gradient ζ (EuclideanSpace.finAddEquivProd (q.symm x)).1) ∂V.weight| ≤ M * (V.weight (closedBall 0 (σ / 2) ∩ (V.support \ q '' graphOver f (closedBall 0 (σ / 2))))).toReal + M * ∫ x in closedBall 0 σ, hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight + M * (σ / 4) * ∫ x in closedBall 0 (σ / 2), ‖H x‖ ∂V.weight`

## Sibling prerequisites

- `root.tilt_excess_decay-a1.graph_weak_equation-a1.lipschitz_graph_area-a1`
- `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tilt_algebra-a1`
- `root.tilt_excess_decay-a1.graph_weak_equation-a1.vertical_first_variation-a1`
- `root.lipschitz_approximation-a1.graph_coordinates-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
