# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1.dyadic_radii-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-4f181635e7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1`
- Child key: `dyadic_radii`
- Declaration: `Submission.dimred_mbl_dtsd_sh_dyadic_good_radii`
- Exact Lean type: `(∀ (P : ℕ) (μ μ' : Measure (Euclid P)) (f : Euclid P → ℝ) (ρ : ℝ) (B : ℝ≥0∞), IsFiniteMeasure μ → IsFiniteMeasure μ' → Measurable f → 0 < ρ → μ {x | f x < ρ} ≤ B → ∃ r ∈ Ioo (ρ / 2) ρ, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | r - h < f x ∧ f x < r}) (𝓝[>] 0) ≤ ENNReal.ofReal (4 / ρ) * B ∧ liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ' {x | r - h < f x ∧ f x < r}) (𝓝[>] 0) < ∞) → ∀ (P m : ℕ) (μ μ' : Measure (Euclid P)) (d : Euclid P → ℝ) (C : NNReal) (M M' : ℝ≥0∞), IsFiniteMeasure μ → IsFiniteMeasure μ' → Measurable d → M ≠ ∞ → M' ≠ ∞ → (∀ r : ℝ, 0 < r → r ≤ 1 / 4 → μ {x | d x < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * M ∧ μ' {x | d x < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * M') → ∃ r : ℕ → ℝ, (∀ j, (1 / 2 : ℝ) ^ (j + 3) < r j ∧ r j < (1 / 2 : ℝ) ^ (j + 2)) ∧ StrictAnti r ∧ (∀ j, μ {x | d x < r j} ≤ C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) * M ∧ μ' {x | d x < r j} ≤ C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) * M') ∧ Tendsto (fun j => μ {x | d x < r j}) atTop (𝓝 0) ∧ Tendsto (fun j => μ' {x | d x < r j}) atTop (𝓝 0) ∧ (∀ j, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | r j - h < d x ∧ d x < r j}) (𝓝[>] 0) ≤ 4 * C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 1))) * M) ∧ (∀ j, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ' {x | r j - h < d x ∧ d x < r j}) (𝓝[>] 0) < ∞)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
