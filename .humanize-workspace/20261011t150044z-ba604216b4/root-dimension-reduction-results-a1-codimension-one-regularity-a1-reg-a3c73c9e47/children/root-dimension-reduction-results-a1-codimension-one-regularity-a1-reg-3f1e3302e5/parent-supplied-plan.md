# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_divergence-a1.field_regularity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-3f1e3302e5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_divergence-a1`
- Child key: `field_regularity`
- Declaration: `Submission.codim1_lur_cd_pullback_field_regularity`
- Exact Lean type: `∀ (P n : ℕ) (D : Set (Euclid (n + 1))) (G : Euclid (n + 1) → Euclid P) (ω : DifferentialForm (Euclid P) n) (Φ : Euclid (n + 1) → Euclid (n + 1)), IsOpen D → ContDiffOn ℝ 2 G D → ContDiff ℝ (⊤ : ℕ∞) ω → IsCompact (D ∩ G ⁻¹' tsupport ω) → Φ = D.indicator (fun v => ∑ j : Fin (n + 1), ((-1 : ℝ) ^ (j : ℕ) * ω (G v) (fun k => fderiv ℝ G v (EuclideanSpace.single (j.succAbove k) 1))) • EuclideanSpace.single j (1 : ℝ)) → ContDiff ℝ 1 Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ D`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
