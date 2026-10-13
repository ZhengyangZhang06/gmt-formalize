# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b5d5990773/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1`
- Child key: `hypercone_plane`
- Declaration: `Submission.codim1_deformation_minimal_hypercone_is_plane`
- Exact Lean type: `∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)), 2 ≤ m → m ≤ 6 → Module.finrank ℝ A₀ = m + 1 → M.Nonempty → M ⊆ (A₀ : Set (Euclid P)) → (0 : Euclid P) ∉ M → IsEmbeddedSubmanifold 1 m M → closure M ⊆ insert 0 M → (∀ t : ℝ, 0 < t → ∀ x ∈ M, t • x ∈ M) → (∃ ξ : Euclid P → MultiVector P m, IsOrientation m M ξ) → (∀ K : Set (Euclid P), IsCompact K → μHE[m] (M ∩ K) ≠ ∞) → (∀ Z : Euclid P → Euclid P, ContDiff ℝ (⊤ : ℕ∞) Z → HasCompactSupport Z → (0 : Euclid P) ∉ tsupport Z → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, |t| < t₀ → μHE[m] (M ∩ tsupport Z) ≤ μHE[m] ((fun x => x + t • Z x) '' (M ∩ tsupport Z))) → ∃ H₀ : Submodule ℝ (Euclid P), Module.finrank ℝ H₀ = m ∧ M = (H₀ : Set (Euclid P)) \ {0}`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`
- `root.dimension_reduction_results-a1.regular_point_density-a1.bilipschitz_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
