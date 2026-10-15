# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.truncation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-f1cf4cd76e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1`
- Child key: `truncation`
- Declaration: `Submission.dtc_bc_tc_truncation`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U (m + 1)) (R : ℝ), IsOpen U → 0 < R → closedBall (0 : Euclid P) R ⊆ U → IsIntegerMultiplicity S → (∀ ω : TestFormOn U m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ ball 0 R → S.boundary ω = 0) → ∃ (ρ : ℝ) (Ŝ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), R / 4 < ρ ∧ ρ < R / 2 ∧ IsIntegerMultiplicity Ŝ ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ ball 0 ρ → Ŝ ω = currentEval S (ω : DifferentialForm (Euclid P) (m + 1))) ∧ (∀ β : TestFormOn (univ : Set (Euclid P)) m, tsupport (β : DifferentialForm (Euclid P) m) ⊆ ball 0 ρ → Ŝ.boundary β = 0) ∧ (∀ O : Set (Euclid P), IsOpen O → Ŝ.massOn O ≤ S.massOn O) ∧ Ŝ.mass < ∞ ∧ Ŝ.boundary.mass < ∞`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.radial_slice-a1`
- `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.imrep_restrict-a1`
- `root.density_and_tangent_cones-a1.localize-a1.imrep_current-a1`
- `root.compactness_of_minimizing_currents-a1.mass_equals_rep_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
