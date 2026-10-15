# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.halfspace_rigidity-a1.density_trichotomy-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-fbf483deaa/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.halfspace_rigidity-a1`
- Child key: `density_trichotomy`
- Declaration: `Submission.codim1_rdo_dg_hr_monotone_set_trichotomy`
- Exact Lean type: `∀ (n : ℕ) (F : Set (EuclideanSpace ℝ (Fin n))) (v : EuclideanSpace ℝ (Fin n)), MeasurableSet F → (∀ a : EuclideanSpace ℝ (Fin n), 0 ≤ inner ℝ a v → ∀ᵐ z ∂volume, z ∈ F → z + a ∈ F) → volume F = 0 ∨ volume Fᶜ = 0 ∨ ∃ c : ℝ, volume (symmDiff F {z | c < inner ℝ z v}) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
