# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1.fundamental_lemma-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-fcfbbabdfa/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1`
- Child key: `fundamental_lemma`
- Declaration: `Submission.codim1_hcp_un_fundamental_lemma`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (U M : Set (Euclid P)) (h : Euclid P → ℝ), IsOpen U → M ⊆ U → MeasurableSet M → ContinuousOn h M → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ (M ∩ K) ≠ ∞) → (∀ x ∈ M, ∀ s : ℝ, 0 < s → 0 < μ (M ∩ ball x s)) → (∀ φ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in M, φ x * h x ∂μ = 0) → ∀ x ∈ M, h x = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
