# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.radial_slice-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-77957babf4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1`
- Child key: `radial_slice`
- Declaration: `Submission.dtc_bc_tc_radial_slice_bound`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U (m + 1)) (Rp : IMRep U (m + 1)) (R : ℝ), IsOpen U → 0 < R → closedBall (0 : Euclid P) R ⊆ U → Rp.Represents S → (∀ ω : TestFormOn U m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ ball 0 R → S.boundary ω = 0) → ∃ t σ : ℝ, R / 4 < t ∧ t < R / 2 ∧ ∀ (β : TestFormOn (univ : Set (Euclid P)) m) (s : ℝ), (∀ x, covectorEuclideanNorm ((β : DifferentialForm (Euclid P) m) x) ≤ s) → |∫ x in Rp.carrier ∩ ball 0 t, (Rp.mult x : ℝ) * Rp.orient x (exteriorDerivative (β : DifferentialForm (Euclid P) m) x) ∂μHE[m + 1]| ≤ σ * s`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.covector_gram_bounds-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
