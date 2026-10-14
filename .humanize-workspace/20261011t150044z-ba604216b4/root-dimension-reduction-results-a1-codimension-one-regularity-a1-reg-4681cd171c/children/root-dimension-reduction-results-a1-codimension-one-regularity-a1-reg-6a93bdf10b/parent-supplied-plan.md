# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1.halving_step-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-6a93bdf10b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1`
- Child key: `halving_step`
- Declaration: `Submission.codim1_rdo_dg_rc_halving_step`
- Exact Lean type: `∀ (m : ℕ) (D : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)), (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ y, ‖ν y‖ = 1) → (∀ᵐ y ∂μ, Tendsto (fun r : ℝ => μ (closedBall y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 1) ∧ Tendsto (fun r : ℝ => μ ({z | (1 / 4 : ℝ) * ‖z - y‖ ≤ |inner ℝ (z - y) (ν y)|} ∩ closedBall y r) / ENNReal.ofReal (r ^ m)) (𝓝[>] 0) (𝓝 0)) → ∀ U : Set (Euclid (m + 1)), IsOpen U → IsCompact (closure U) → closure U ⊆ D → ∃ Γ : Set (Euclid (m + 1)), IsClosed Γ ∧ CountablyRectifiable m Γ ∧ μ (U \ Γ) ≤ μ U / 2`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1.uniform_compact-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1.compact_cover-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
