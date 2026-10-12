# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_campanato-a1.campanato_from_tilt-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-campanato-from-tilt-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.graph_campanato-a1`
- Child key: `campanato_from_tilt`
- Declaration: `Submission.allard52_campanato_from_tilt`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (S : Amb n ℓ → Submodule ℝ (Amb n ℓ)) (R A e : ℝ), 0 < R → closedBall (0 : Amb n ℓ) R ⊆ U → f 0 = 0 → LipschitzOnWith 1 f (closedBall 0 R) → V.support ∩ closedBall 0 R = q '' graphOver f (closedBall 0 R) ∩ closedBall 0 R → AEStronglyMeasurable V.tangentProj V.weight → (∀ Φ : Amb n ℓ → (Amb n ℓ →L[ℝ] Amb n ℓ) → ℝ≥0∞, Measurable (Function.uncurry Φ) → ∀ D : Set (Rn n), MeasurableSet D → D ⊆ ball 0 (R / 2) → ∫⁻ x in D, Φ (q (graphPoint x (f x))) ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ f x v))).map q.toLinearEquiv.toLinearMap).starProjection ≤ ∫⁻ y in q '' graphOver f D, Φ y (V.tangentProj y) ∂V.weight) → (∀ ζ ∈ V.support ∩ closedBall 0 (R / 2), ∀ s : ℝ, 0 < s → s ≤ R / 2 → V.tiltExcess ζ s (S ζ) ≤ A * (s / R) ^ e) → ∀ z ∈ closedBall (0 : Rn n) (R / 4), ∀ s : ℝ, 0 < s → s ≤ R / 4 → ∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ f x v))).map q.toLinearEquiv.toLinearMap).starProjection - (S (q (graphPoint z (f z)))).starProjection)) ≤ ENNReal.ofReal (A * s ^ n * (s / R) ^ e)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
