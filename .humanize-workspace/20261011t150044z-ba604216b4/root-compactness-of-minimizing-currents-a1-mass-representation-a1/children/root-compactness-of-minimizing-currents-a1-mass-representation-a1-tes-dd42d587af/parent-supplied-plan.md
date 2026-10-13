# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.testform_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-tes-dd42d587af/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1`
- Child key: `testform_extension`
- Declaration: `Submission.cmr_testForm_extension_functional`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (d : ℕ) (c : Covector (Euclid P) n ≃L[ℝ] EuclideanSpace ℝ (Fin d)), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → (∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖c α‖) → ∃ L : CompactlySupportedContinuousMap U (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] ℝ, (∀ (ω : TestFormOn U n) (g : CompactlySupportedContinuousMap U (EuclideanSpace ℝ (Fin d))), (∀ x : U, g x = c ((ω : DifferentialForm (Euclid P) n) x)) → L g = T ω) ∧ ∀ K : Set U, IsCompact K → ∃ M : ℝ, ∀ g : CompactlySupportedContinuousMap U (EuclideanSpace ℝ (Fin d)), tsupport g ⊆ K → (∀ x, ‖g x‖ ≤ 1) → |L g| ≤ M`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.mass_representation-a1.eval_mass_bound-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.smooth_unit_approximation-a1.mollify_unit_field-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
