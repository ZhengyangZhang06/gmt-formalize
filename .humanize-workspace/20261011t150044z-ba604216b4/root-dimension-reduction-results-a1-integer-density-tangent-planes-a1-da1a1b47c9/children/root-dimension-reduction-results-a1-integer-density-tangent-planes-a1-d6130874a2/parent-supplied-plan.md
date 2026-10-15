# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.box_mass_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-d6130874a2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1`
- Child key: `box_mass_limit`
- Declaration: `Submission.idtp_cse_bml_box_mass_limit`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (m : ℕ) (s : ℝ), IsFiniteMeasureOnCompacts μ → Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → 0 < s → (∀ s' : ℝ, 0 < s' → s' ≤ s → μ ({x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s' ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s' ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} \ ball a (3 * s')) = 0) → (∀ lams : ℕ → ℝ, (∀ j, 0 < lams j) → Tendsto lams atTop (𝓝 0) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ g : Euclid P → ℝ, Continuous g → HasCompactSupport g → Tendsto (fun j => (lams (φ j))⁻¹ ^ 2 * ∫ x, g (dilation a (lams (φ j)) x) ∂μ) atTop (𝓝 ((m : ℝ) * ∫ x in (Q : Set (Euclid P)), g x ∂μHE[2]))) → Tendsto (fun s' : ℝ => μ {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s' ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s' ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} / ENNReal.ofReal (s' ^ 2)) (𝓝[>] 0) (𝓝 (4 * (m : ℝ≥0∞)))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.subseq_criterion-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.box_inclusions-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.square_measure-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.rescaled_portmanteau-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
