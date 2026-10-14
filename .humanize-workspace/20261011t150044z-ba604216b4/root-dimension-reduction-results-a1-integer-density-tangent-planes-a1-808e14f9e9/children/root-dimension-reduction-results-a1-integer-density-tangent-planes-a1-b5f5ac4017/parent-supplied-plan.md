# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.rescaled_portmanteau-a1.dilation_map_rescaling-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-b5f5ac4017/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.rescaled_portmanteau-a1`
- Child key: `dilation_map_rescaling`
- Declaration: `Submission.idtp_cse_bml_rpm_dilation_map`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (a : Euclid P) (lam : ℝ), IsFiniteMeasureOnCompacts μ → 0 < lam → (∀ K : Set (Euclid P), IsCompact K → Measure.map (dilation a lam) (ENNReal.ofReal (lam⁻¹ ^ 2) • μ) K < ∞) ∧ (∀ S : Set (Euclid P), MeasurableSet S → Measure.map (dilation a lam) (ENNReal.ofReal (lam⁻¹ ^ 2) • μ) S = ENNReal.ofReal (lam⁻¹ ^ 2) * μ (dilation a lam ⁻¹' S)) ∧ ∀ g : Euclid P → ℝ, Continuous g → ∫ x, g x ∂(Measure.map (dilation a lam) (ENNReal.ofReal (lam⁻¹ ^ 2) • μ)) = lam⁻¹ ^ 2 * ∫ x, g (dilation a lam x) ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
