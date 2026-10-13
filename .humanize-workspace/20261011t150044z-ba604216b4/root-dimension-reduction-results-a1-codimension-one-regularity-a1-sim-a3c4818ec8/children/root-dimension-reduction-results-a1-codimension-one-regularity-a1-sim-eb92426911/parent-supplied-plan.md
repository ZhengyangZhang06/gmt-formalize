# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.codazzi-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-eb92426911/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1`
- Child key: `codazzi`
- Declaration: `Submission.codim1_hcp_sc_weingarten_codazzi`
- Exact Lean type: `∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ν : Euclid P → Euclid P), Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → (∀ r : ℕ, IsEmbeddedSubmanifold r m M) → (∃ O : Set (Euclid P), IsOpen O ∧ M ⊆ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ν O) → (∀ x ∈ M, ν x ∈ A₀ ∧ ‖ν x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν x) v = 0) → ∀ x ∈ M, ∀ a ∈ tangentSpace M x, ∀ b ∈ tangentSpace M x, fderiv ℝ ν x a ∈ tangentSpace M x ∧ inner ℝ (fderiv ℝ ν x a) b = inner ℝ (fderiv ℝ ν x b) a ∧ ∀ d ∈ tangentSpace M x, inner ℝ (fderivWithin ℝ (fun y => (fderiv ℝ ν y).comp (Submodule.span ℝ (tangentSpace M y)).starProjection) M x a b) d = inner ℝ (fderivWithin ℝ (fun y => (fderiv ℝ ν y).comp (Submodule.span ℝ (tangentSpace M y)).starProjection) M x b a) d ∧ inner ℝ (fderivWithin ℝ (fun y => (fderiv ℝ ν y).comp (Submodule.span ℝ (tangentSpace M y)).starProjection) M x a b) d = inner ℝ (fderivWithin ℝ (fun y => (fderiv ℝ ν y).comp (Submodule.span ℝ (tangentSpace M y)).starProjection) M x a d) b`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.tangent_fderiv-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.normal_complement-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
