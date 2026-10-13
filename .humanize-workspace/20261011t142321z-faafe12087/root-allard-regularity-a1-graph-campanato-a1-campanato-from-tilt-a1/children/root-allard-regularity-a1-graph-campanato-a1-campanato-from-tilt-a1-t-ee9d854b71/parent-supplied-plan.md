# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_campanato-a1.campanato_from_tilt-a1.tilt_lintegral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-campanato-from-tilt-a1-t-ee9d854b71/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.graph_campanato-a1.campanato_from_tilt-a1`
- Child key: `tilt_lintegral`
- Declaration: `Submission.allard52_cft_tilt_lintegral_eq`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), AEStronglyMeasurable V.tangentProj V.weight → ∀ (ζ : Amb n ℓ) (s : ℝ) (T : Submodule ℝ (Amb n ℓ)), 0 < s → V.weight (closedBall ζ s) < ⊤ → ∫⁻ y in closedBall ζ s, ENNReal.ofReal (hsNormSq (V.tangentProj y - T.starProjection)) ∂V.weight = ENNReal.ofReal (s ^ n * V.tiltExcess ζ s T)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
