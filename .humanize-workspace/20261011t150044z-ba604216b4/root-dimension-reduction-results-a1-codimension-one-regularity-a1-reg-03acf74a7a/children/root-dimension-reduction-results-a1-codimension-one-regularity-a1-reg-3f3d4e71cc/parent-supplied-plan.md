# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.halfspace_rigidity-a1.translation_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-3f3d4e71cc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.halfspace_rigidity-a1`
- Child key: `translation_identity`
- Declaration: `Submission.codim1_rdo_dg_hr_translate_integral_eq`
- Exact Lean type: `∀ (n : ℕ) (F : Set (EuclideanSpace ℝ (Fin n))) (ζ : EuclideanSpace ℝ (Fin n) → ℝ) (w : EuclideanSpace ℝ (Fin n)) (t : ℝ), MeasurableSet F → ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ z in F, ζ (z - t • w) = (∫ z in F, ζ z) - ∫ s in (0 : ℝ)..t, ∫ z in F, fderiv ℝ ζ (z - s • w) w`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
