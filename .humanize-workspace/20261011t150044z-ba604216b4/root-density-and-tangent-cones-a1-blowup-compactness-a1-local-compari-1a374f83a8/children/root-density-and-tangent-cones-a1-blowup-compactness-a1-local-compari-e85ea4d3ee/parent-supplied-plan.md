# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1.smooth_leibniz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-e85ea4d3ee/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1`
- Child key: `smooth_leibniz`
- Declaration: `Submission.dtc_bc_lc_sl_ll_smooth_leibniz`
- Exact Lean type: `∀ (P m : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (RT : IMRep (univ : Set (Euclid P)) (m + 2)) (RB : IMRep (univ : Set (Euclid P)) (m + 1)) (g : Euclid P → ℝ), RT.Represents T → RB.Represents T.boundary → ContDiff ℝ (⊤ : ℕ∞) g → ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), (∫ x in RB.carrier, (RB.mult x : ℝ) * g x * RB.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1]) - (∫ x in RT.carrier, (RT.mult x : ℝ) * g x * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 2]) = ∫ x in RT.carrier, (RT.mult x : ℝ) * RT.orient x (ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight ((ω : DifferentialForm (Euclid P) (m + 1)) x))) ∂μHE[m + 2]`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.slicing-a1.cutoff_defect-a1.defect_identity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
