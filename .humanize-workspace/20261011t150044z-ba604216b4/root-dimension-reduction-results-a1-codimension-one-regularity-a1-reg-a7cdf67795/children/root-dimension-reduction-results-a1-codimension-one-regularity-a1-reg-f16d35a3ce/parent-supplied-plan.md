# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.bv_compactness-a1.mollify_l1-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-f16d35a3ce/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.bv_compactness-a1`
- Child key: `mollify_l1`
- Declaration: `Submission.codim1_rdo_dg_bvc_mollify_l1_le`
- Exact Lean type: `∀ (n : ℕ) (F : Set (Euclid n)) (R C ε : ℝ) (ρ : Euclid n → ℝ), MeasurableSet F → ε ≤ 1 → Continuous ρ → HasCompactSupport ρ → (∀ y, 0 ≤ ρ y) → ∫ y, ρ y = 1 → support ρ ⊆ ball (0 : Euclid n) ε → (∀ g : Euclid n → Euclid n, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ ball (0 : Euclid n) (R + 1) → (∀ z, ‖g z‖ ≤ 1) → ∫ z in F, LinearMap.trace ℝ (Euclid n) (fderiv ℝ g z : Euclid n →ₗ[ℝ] Euclid n) ≤ C) → ∫ z in ball (0 : Euclid n) R, |F.indicator (fun _ => (1 : ℝ)) z - ∫ y, ρ y * F.indicator (fun _ => (1 : ℝ)) (z - y)| ≤ ε * C`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.bv_compactness-a1.translation_l1-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
