# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.rescaled_portmanteau-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-808e14f9e9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1`
- Child key: `rescaled_portmanteau`
- Declaration: `Submission.idtp_cse_bml_rescaled_portmanteau`
- Exact Lean type: `∀ (P : ℕ) (μ ν : Measure (Euclid P)) (a : Euclid P) (lams : ℕ → ℝ), IsFiniteMeasureOnCompacts μ → IsFiniteMeasureOnCompacts ν → (∀ j, 0 < lams j) → (∀ g : Euclid P → ℝ, Continuous g → HasCompactSupport g → Tendsto (fun j => (lams j)⁻¹ ^ 2 * ∫ x, g (dilation a (lams j) x) ∂μ) atTop (𝓝 (∫ x, g x ∂ν))) → (∀ K : Set (Euclid P), IsCompact K → limsup (fun j => ENNReal.ofReal ((lams j)⁻¹ ^ 2) * μ (dilation a (lams j) ⁻¹' K)) atTop ≤ ν K) ∧ ∀ U : Set (Euclid P), IsOpen U → ν U ≤ liminf (fun j => ENNReal.ofReal ((lams j)⁻¹ ^ 2) * μ (dilation a (lams j) ⁻¹' U)) atTop`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
