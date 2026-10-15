# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.tilt_decay-a1.excess_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-9fb004f78a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.tilt_decay-a1`
- Child key: `excess_bound`
- Declaration: `Submission.idtp_cse_bml_td_excess_bound`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (d ϑ : Euclid P → ℝ) (a : Euclid P) (t : ℝ), 0 < t → (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → AEStronglyMeasurable d μ → (∀ᵐ x ∂μ, |d x| ≤ 1) → Continuous ϑ → HasCompactSupport ϑ → (∀ x, 0 ≤ ϑ x) → (∀ x : Euclid P, ‖x‖ < 3 → ϑ x = 1) → (∫⁻ x in ball a (3 * t), ENNReal.ofReal (1 - |d x|) ∂μ) / ENNReal.ofReal (t ^ 2) ≤ ENNReal.ofReal (t⁻¹ ^ 2 * ∫ x, ϑ (dilation a t x) ∂μ - |t⁻¹ ^ 2 * ∫ x, ϑ (dilation a t x) * d x ∂μ|)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
