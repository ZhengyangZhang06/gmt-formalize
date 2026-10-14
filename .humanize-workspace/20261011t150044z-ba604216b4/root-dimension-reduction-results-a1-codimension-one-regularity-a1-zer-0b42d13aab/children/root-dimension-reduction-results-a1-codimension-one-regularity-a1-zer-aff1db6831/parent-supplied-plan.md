# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.centres_near-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-aff1db6831/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1`
- Child key: `centres_near`
- Declaration: `Submission.codim1_zsl_blowUp_centres_near`
- Exact Lean type: `∀ (P n : ℕ) (U N E : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (T : GeometricCurrentOn U n) (x : Euclid P) (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i) (S : GeometricCurrentOn (univ : Set (Euclid P)) n), (closure N \ N) ∩ U = ∅ → E ⊆ N → IsBoundaryOfRegion T E ξN → x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → ConvergesWeakly (fun i => blowUp T (xs i) (lams i) (hlams i).ne') S → S.support.Nonempty → x ∈ N ∧ ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ i, ∃ p ∈ N, dist p (xs i) ≤ C₀ * lams i`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.blowup_region-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
