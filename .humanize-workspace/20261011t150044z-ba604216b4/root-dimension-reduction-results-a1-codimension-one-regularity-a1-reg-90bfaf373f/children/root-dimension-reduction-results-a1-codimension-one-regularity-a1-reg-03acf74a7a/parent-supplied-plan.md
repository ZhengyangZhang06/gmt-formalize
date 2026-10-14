# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.halfspace_rigidity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-03acf74a7a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1`
- Child key: `halfspace_rigidity`
- Declaration: `Submission.codim1_rdo_dg_halfspace_rigidity`
- Exact Lean type: `∀ (m : ℕ) (F₀ : Set (Euclid (m + 1))) (v : Euclid (m + 1)), ‖v‖ = 1 → MeasurableSet F₀ → (∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∀ w : Euclid (m + 1), inner ℝ w v = 0 → ∫ z in F₀, fderiv ℝ ζ z w = 0) → (∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → (∀ z, 0 ≤ ζ z) → ∫ z in F₀, fderiv ℝ ζ z v ≤ 0) → volume F₀ = 0 ∨ volume F₀ᶜ = 0 ∨ ∃ c : ℝ, volume (symmDiff F₀ {z | c < inner ℝ z v}) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
