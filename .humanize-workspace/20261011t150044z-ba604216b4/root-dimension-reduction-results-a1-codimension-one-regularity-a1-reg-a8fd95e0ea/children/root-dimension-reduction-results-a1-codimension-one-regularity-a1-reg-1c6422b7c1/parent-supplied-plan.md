# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.piece_tangent-a1.area_jacobian-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-1c6422b7c1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.piece_tangent-a1`
- Child key: `area_jacobian`
- Declaration: `Submission.codim1_lurpt_piece_area_jacobian`
- Exact Lean type: `∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (L : NNReal), LipschitzWith L F → MeasurableSet B → InjOn F B → ∃ J : Euclid n → ℝ, Measurable J ∧ (∀ a, 0 ≤ J a ∧ J a ≤ (L : ℝ) ^ n) ∧ (∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in F '' B, g y ∂μHE[n] = ∫⁻ x in B, ENNReal.ofReal (J x) * g (F x) ∂volume) ∧ ∀ (a : Euclid n) (S : Set (Euclid n)), μHE[n] (fderiv ℝ F a '' S) = ENNReal.ofReal (J a) * volume S`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
