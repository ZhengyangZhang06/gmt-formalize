# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.cauchy_subseq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-e77772e34b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1`
- Child key: `cauchy_subseq`
- Declaration: `Submission.dtc_bc_lc_fd_cauchy_subseq`
- Exact Lean type: `∀ (P m : ℕ) (L : Set (Euclid P)) (X : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsCompact L → (∀ ε : ℝ≥0∞, 0 < ε → ∃ 𝒬 : Set (GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), 𝒬.Finite ∧ ∀ j, ∃ Q ∈ 𝒬, ∃ (R : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity R ∧ R.support ⊆ L ∧ X j - Q - S = R.boundary ∧ R.mass + S.mass ≤ ε) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ r, ∃ (R : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity R ∧ R.support ⊆ L ∧ X (φ (r + 1)) - X (φ r) - S = R.boundary ∧ R.mass + S.mass ≤ (2⁻¹ : ℝ≥0∞) ^ r`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.cauchy_subseq-a1.diagonal_subseq-a1`
- `root.density_and_tangent_cones-a1.vanish_off_support-a1`
- `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.support_of_vanishing-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
