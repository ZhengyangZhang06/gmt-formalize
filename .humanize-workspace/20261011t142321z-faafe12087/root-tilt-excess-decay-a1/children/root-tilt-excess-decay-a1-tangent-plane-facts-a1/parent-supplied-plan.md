# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.tangent_plane_facts-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-tangent-plane-facts-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1`
- Child key: `tangent_plane_facts`
- Declaration: `Submission.ted_tangent_plane_facts`
- Exact Lean type: `∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ V : RectifiableVarifold n ℓ U, (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P) ∧ (∀ᵐ x ∂V.weight, ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) ∧ AEStronglyMeasurable V.tangentProj V.weight ∧ (∀ᵐ x ∂V.weight, V.HasDensity x (V.mult x)) ∧ ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (R : ℝ) (L : ℝ≥0), LipschitzOnWith L f (closedBall 0 R) → ∀ᵐ x ∂V.weight, ∀ x' ∈ ball (0 : Rn n) R, x = q (graphPoint x' (f x')) → DifferentiableAt ℝ f x' → V.tangentProj x = (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (fderiv ℝ f x' v)))).starProjection`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
