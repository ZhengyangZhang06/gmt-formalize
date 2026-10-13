# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.deformation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-57991f1e6d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1`
- Child key: `deformation`
- Declaration: `Submission.dtc_bc_lc_fd_deformation`
- Exact Lean type: `∀ (P m : ℕ), m + 1 < P → ∃ c : NNReal, ∀ (K : Set (Euclid P)) (Λ : NNReal) (ε : ℝ≥0∞), IsCompact K → 0 < ε → ∃ 𝒬 : Set (GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), 𝒬.Finite ∧ ∀ A : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity A → A.support ⊆ K → A.mass ≤ Λ → A.boundary.mass ≤ Λ → ∃ Q ∈ 𝒬, ∃ (R : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity R ∧ IsIntegerMultiplicity Q.boundary ∧ A - Q - S = R.boundary ∧ R.mass + S.mass ≤ ε ∧ Q.boundary.mass ≤ c * A.boundary.mass ∧ R.support ⊆ cthickening 1 K`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.density_and_tangent_cones-a1.mass_eq_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
