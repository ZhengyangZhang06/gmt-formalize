# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1.total_mass-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-9a448cbbce/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1`
- Child key: `total_mass`
- Declaration: `Submission.idtp_fons_cc_psf_total_mass`
- Exact Lean type: `∀ (P n : ℕ) (μ μ₀ : Measure (Euclid P)) (z : Euclid P) (r : ℝ), 0 < r → μ (ball z (2 * r)) ≠ 0 → μ (ball z (2 * r)) ≠ ∞ → μ₀ = ENNReal.ofReal (r⁻¹ ^ n) • (μ.restrict (ball z (2 * r))).map (dilation z r) → μ₀ univ ≠ 0 ∧ μ₀ univ ≠ ∞ ∧ μ₀ (ball (0 : Euclid P) 2)ᶜ = 0 ∧ ∀ (x : Euclid P) (lam : ℝ), 0 < lam → (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) univ ≠ 0 ∧ (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) univ ≠ ∞`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
