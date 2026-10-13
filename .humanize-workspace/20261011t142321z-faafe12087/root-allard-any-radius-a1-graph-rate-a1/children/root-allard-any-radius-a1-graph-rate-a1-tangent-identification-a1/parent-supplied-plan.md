# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.graph_rate-a1.tangent_identification-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-tangent-identification-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.graph_rate-a1`
- Child key: `tangent_identification`
- Declaration: `Submission.any_radius_gr_tangent_identification`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), AEStronglyMeasurable V.tangentProj V.weight → ∀ (ζ : Amb n ℓ) (S : Submodule ℝ (Amb n ℓ)) (c s₀ : ℝ), 0 < c → 0 < s₀ → (∀ s : ℝ, 0 < s → s ≤ s₀ → ENNReal.ofReal (c * s ^ n) ≤ V.weight (closedBall ζ s) ∧ V.weight (closedBall ζ s) < ⊤) → Tendsto (fun s : ℝ => (V.weight (closedBall ζ s))⁻¹ * ∫⁻ y in closedBall ζ s, ENNReal.ofReal (hsNormSq (V.tangentProj y - V.tangentProj ζ)) ∂V.weight) (𝓝[>] 0) (𝓝 0) → Tendsto (fun s : ℝ => V.tiltExcess ζ s S) (𝓝[>] 0) (𝓝 0) → V.tangentProj ζ = S.starProjection`

## Sibling prerequisites

- `root.allard_any_radius-a1.graph_rate-a1.la_basics-a1`
- `root.allard_any_radius-a1.graph_rate-a1.tilt_integrals-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
