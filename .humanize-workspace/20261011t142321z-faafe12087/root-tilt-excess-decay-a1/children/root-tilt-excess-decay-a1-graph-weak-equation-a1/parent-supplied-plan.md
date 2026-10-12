# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1`
- Child key: `graph_weak_equation`
- Declaration: `Submission.ted_graph_weak_equation`
- Exact Lean type: `∀ n ℓ : ℕ, 1 ≤ n → ∀ Kb : ℝ, 0 ≤ Kb → ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → AEStronglyMeasurable V.tangentProj V.weight → ∀ σ : ℝ, 0 < σ → closedBall 0 σ ⊆ U → ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ), LipschitzOnWith 1 f (closedBall 0 (σ / 2)) → (∀ x ∈ closedBall (0 : Rn n) (σ / 2), ‖f x‖ ≤ σ / 16) → (∀ x ∈ V.support ∩ closedBall 0 σ, infDist x (rotatedPlane q : Set (Amb n ℓ)) ≤ σ / 16) → (∀ᵐ x ∂V.weight, ∀ x' ∈ ball (0 : Rn n) (σ / 2), x = q (graphPoint x' (f x')) → DifferentiableAt ℝ f x' → V.tangentProj x = (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (fderiv ℝ f x' v)))).starProjection) → ∀ κ E h : ℝ, 0 ≤ κ → κ ≤ 1 → 0 ≤ E → 0 ≤ h → (∀ᵐ x ∂V.weight, x ∈ closedBall 0 σ → 1 ≤ V.mult x ∧ V.mult x ≤ 1 + κ) → (μHE[n] : Measure (Amb n ℓ)) ((V.support ∩ closedBall 0 σ) \ V.carrier) = 0 → ∫ x in closedBall 0 σ, hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight ≤ E * σ ^ n → V.weight (closedBall 0 (σ / 2) ∩ (V.support \ q '' graphOver f (closedBall 0 (σ / 2)))) + (μHE[n] : Measure (Amb n ℓ)) (closedBall 0 (σ / 2) ∩ (q '' graphOver f (closedBall 0 (σ / 2)) \ V.support)) ≤ ENNReal.ofReal (Kb * E * σ ^ n) → ∫ x in closedBall 0 (σ / 2), ‖H x‖ ∂V.weight ≤ h * σ ^ (n - 1) → (∫ x in ball (0 : Rn n) (3 * σ / 8), hsNormSq (fderiv ℝ f x) ≤ C * E * σ ^ n) ∧ ∀ ζ : Rn n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 (σ / 4) → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ j : Fin ℓ, |∫ x in ball (0 : Rn n) (σ / 4), inner ℝ (gradient (fun y => f y j) x) (gradient ζ x)| ≤ C * (E + h + κ * Real.sqrt E) * M * σ ^ n`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
