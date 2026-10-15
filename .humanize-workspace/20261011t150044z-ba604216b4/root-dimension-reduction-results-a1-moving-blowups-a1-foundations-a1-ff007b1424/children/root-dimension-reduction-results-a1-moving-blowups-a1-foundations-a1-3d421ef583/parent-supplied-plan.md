# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1.testform_extension-a1.limit_functional-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-foundations-a1-3d421ef583/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1.testform_extension-a1`
- Child key: `limit_functional`
- Declaration: `Submission.dimred_mbl_fnd_tfe_exists_limit_functional`
- Exact Lean type: `∀ (P n d : ℕ) (c : Covector (Euclid P) n ≃L[ℝ] EuclideanSpace ℝ (Fin d)) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (m : Set (Euclid P) → ℝ), (∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖c α‖) → (∀ (W : Set (Euclid P)) (ω : TestFormOn U n) (r : ℝ), IsOpen W → CompactlyContained W U → tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ r) → |T ω| ≤ r * m W) → ∃ Φ : (Euclid P → Covector (Euclid P) n) → ℝ, ∀ (G : Euclid P → Covector (Euclid P) n) (W : Set (Euclid P)) (ωs : ℕ → TestFormOn U n) (εs : ℕ → ℝ), IsOpen W → CompactlyContained W U → (∀ k, tsupport (ωs k : DifferentialForm (Euclid P) n) ⊆ W) → (∀ k x, covectorEuclideanNorm ((ωs k : DifferentialForm (Euclid P) n) x - G x) ≤ εs k) → Tendsto εs atTop (𝓝 0) → Tendsto (fun k => T (ωs k)) atTop (𝓝 (Φ G))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
