# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-1a374f83a8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1`
- Child key: `lipschitz_leibniz`
- Declaration: `Submission.dtc_bc_lc_sl_lipschitz_leibniz`
- Exact Lean type: `∀ (P m : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (RT : IMRep (univ : Set (Euclid P)) (m + 2)) (RB : IMRep (univ : Set (Euclid P)) (m + 1)) (h : Euclid P → ℝ) (K : NNReal) (H : Euclid P → Euclid P), RT.Represents T → RB.Represents T.boundary → LipschitzWith K h → Measurable H → (∀ x, ‖H x‖ ≤ K) → (∀ᵐ x ∂(μHE[m + 2].restrict RT.carrier), HasApproximateTangentSpaceAt (m + 2) RT.carrier x (approxTangentPlane (m + 2) RT.carrier x) ∧ H x ∈ approxTangentPlane (m + 2) RT.carrier x ∧ ∀ ε : ℝ, 0 < ε → Tendsto (fun r : ℝ => μHE[m + 2] (RT.carrier ∩ ball x r ∩ {y | ε * ‖y - x‖ < |h y - h x - inner ℝ (H x) (y - x)|}) / ENNReal.ofReal (r ^ (m + 2))) (𝓝[>] 0) (𝓝 0)) → ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), (∫ x in RB.carrier, (RB.mult x : ℝ) * h x * RB.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1]) - (∫ x in RT.carrier, (RT.mult x : ℝ) * h x * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 2]) = ∫ x in RT.carrier, (RT.mult x : ℝ) * RT.orient x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (H x)).smulRight ((ω : DifferentialForm (Euclid P) (m + 1)) x))) ∂μHE[m + 2]`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_pieces-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.compactness_of_minimizing_currents-a1.slicing-a1.cutoff_defect-a1.defect_identity-a1`
- `root.compactness_of_minimizing_currents-a1.slicing-a1.lipschitz_smoothing-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
