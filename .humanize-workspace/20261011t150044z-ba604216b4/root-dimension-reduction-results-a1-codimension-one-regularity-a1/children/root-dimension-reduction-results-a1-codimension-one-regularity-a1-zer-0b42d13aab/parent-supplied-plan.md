# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1`
- Child key: `zero_scale_limit_plane`
- Declaration: `Submission.codim1_zero_scale_limit_offset_plane`
- Exact Lean type: `∀ (P n : ℕ) (U N E : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (T : GeometricCurrentOn U n) (x : Euclid P) (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i) (S : GeometricCurrentOn (univ : Set (Euclid P)) n), 1 ≤ n → IsOpen U → InClassO n U N ξN → MeasurableSet E → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN → x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → (∃ C r₀ : ℝ, 0 < r₀ ∧ ∀ y ∈ ball x r₀, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ → T.massOn (ball y ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → ConvergesWeakly (fun i => blowUp T (xs i) (lams i) (hlams i).ne') S → S.support.Nonempty → ∃ (Q : Submodule ℝ (Euclid P)) (a : Euclid P) (F : Set (Euclid P)) (ξA : MultiVector P (n + 1)), Module.finrank ℝ Q = n + 1 ∧ InClassO n (univ : Set (Euclid P)) {y | y + a ∈ Q} (fun _ => ξA) ∧ MeasurableSet F ∧ F ⊆ {y | y + a ∈ Q} ∧ IsBoundaryOfRegion S F (fun _ => ξA)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_scaling-a1.hausdorff_scaling-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.unit_orientation_duality-a1`
- `root.regular_set_dense-a1.integer_combination-a1.orientation_sign-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
