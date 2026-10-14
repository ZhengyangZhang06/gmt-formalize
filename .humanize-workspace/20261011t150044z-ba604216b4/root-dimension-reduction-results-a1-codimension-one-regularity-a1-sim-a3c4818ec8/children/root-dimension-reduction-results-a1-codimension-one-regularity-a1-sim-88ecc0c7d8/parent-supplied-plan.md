# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.cone_defect-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-88ecc0c7d8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1`
- Child key: `cone_defect`
- Declaration: `Submission.codim1_hcp_sc_cone_simons_defect`
- Exact Lean type: `∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ν : Euclid P → Euclid P), Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → (0 : Euclid P) ∉ M → (∀ r : ℕ, IsEmbeddedSubmanifold r m M) → (∀ t : ℝ, 0 < t → ∀ x ∈ M, t • x ∈ M) → (∃ O : Set (Euclid P), IsOpen O ∧ M ⊆ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ν O) → (∀ x ∈ M, ν x ∈ A₀ ∧ ‖ν x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν x) v = 0) → ∀ x ∈ M, 0 < (∑ i : Fin P, ‖fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single i 1))‖ ^ 2) → 2 * (∑ i : Fin P, ‖fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single i 1))‖ ^ 2) ^ 2 / ‖x‖ ^ 2 + (∑ k : Fin P, (fderivWithin ℝ (fun z => ∑ i : Fin P, ‖fderiv ℝ ν z ((Submodule.span ℝ (tangentSpace M z)).starProjection (EuclideanSpace.single i 1))‖ ^ 2) M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single k 1))) ^ 2) / 4 ≤ (∑ i : Fin P, ‖fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single i 1))‖ ^ 2) * (∑ i : Fin P, ∑ j : Fin P, ∑ k : Fin P, (inner ℝ (fderivWithin ℝ (fun y => (fderiv ℝ ν y).comp (Submodule.span ℝ (tangentSpace M y)).starProjection) M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single k 1)) ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single i 1))) ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.tangent_fderiv-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.normal_complement-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.cone_normal-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.codazzi-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
