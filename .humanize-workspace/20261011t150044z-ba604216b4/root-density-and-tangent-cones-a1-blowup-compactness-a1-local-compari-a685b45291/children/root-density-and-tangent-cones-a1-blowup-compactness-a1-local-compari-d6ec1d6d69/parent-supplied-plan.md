# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-d6ec1d6d69/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1`
- Child key: `extension`
- Declaration: `Submission.dtc_bc_lc_pf_pullback_integral_extension`
- Exact Lean type: `∀ (P n : ℕ) (O K : Set (Euclid P)) (f : Euclid P → Euclid P) (ω : TestFormOn (univ : Set (Euclid P)) n), IsOpen O → ContDiffOn ℝ 1 f O → IsCompact K → K ⊆ O → ∃ ωs : ℕ → TestFormOn (univ : Set (Euclid P)) n, ∀ (Y : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), R.Represents Y → Y.support ⊆ K → Tendsto (fun j => Y (ωs j)) atTop (𝓝 (∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[n]))`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.carrier_facts-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
