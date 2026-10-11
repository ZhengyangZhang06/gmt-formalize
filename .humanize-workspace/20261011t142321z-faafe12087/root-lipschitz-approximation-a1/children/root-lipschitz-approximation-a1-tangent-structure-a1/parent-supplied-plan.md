# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_approximation-a1.tangent_structure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1-tangent-structure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_approximation-a1`
- Child key: `tangent_structure`
- Declaration: `Submission.lip_approx_tangent_structure`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U), AEStronglyMeasurable V.tangentProj V.weight ∧ (∀ (T : Submodule ℝ (Amb n ℓ)) (K : Set (Amb n ℓ)), IsCompact K → K ⊆ U → IntegrableOn (fun x => hsNormSq (V.tangentProj x - T.starProjection)) K V.weight) ∧ ∀ᵐ x ∂V.weight, (∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧ V.tangentProj x = T.starProjection) ∧ V.HasDensity x (V.mult x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
