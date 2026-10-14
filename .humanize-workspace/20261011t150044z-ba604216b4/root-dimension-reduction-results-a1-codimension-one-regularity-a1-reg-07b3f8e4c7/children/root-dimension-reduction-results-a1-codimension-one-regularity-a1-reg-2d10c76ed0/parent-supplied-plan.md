# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_approximation-a1.lusin_closed-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-2d10c76ed0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_approximation-a1`
- Child key: `lusin_closed`
- Declaration: `Submission.codim1_rdo_c1a_lusin_isClosed`
- Exact Lean type: `∀ (n : ℕ) {Y : Type} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (g : Euclid n → Y) (B : Set (Euclid n)), Measurable g → MeasurableSet B → ∀ ε : ℝ≥0∞, 0 < ε → ∃ C : Set (Euclid n), C ⊆ B ∧ IsClosed C ∧ ContinuousOn g C ∧ volume (B \ C) < ε`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.lusin_covector-a1.lusin_measurable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
