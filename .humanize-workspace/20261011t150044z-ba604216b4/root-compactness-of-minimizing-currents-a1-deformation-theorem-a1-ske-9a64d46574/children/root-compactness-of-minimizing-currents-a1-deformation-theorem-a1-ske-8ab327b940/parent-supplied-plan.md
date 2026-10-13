# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.good_radius-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-8ab327b940/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1`
- Child key: `good_radius`
- Declaration: `Submission.cmcsd_good_radius`
- Exact Lean type: `∀ (P : ℕ) (μ μ' : Measure (Euclid P)) (f : Euclid P → ℝ) (ρ : ℝ) (B : ℝ≥0∞), IsFiniteMeasure μ → IsFiniteMeasure μ' → Measurable f → 0 < ρ → μ {x | f x < ρ} ≤ B → ∃ r ∈ Ioo (ρ / 2) ρ, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | r - h < f x ∧ f x < r}) (𝓝[>] 0) ≤ ENNReal.ofReal (4 / ρ) * B ∧ liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ' {x | r - h < f x ∧ f x < r}) (𝓝[>] 0) < ∞`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.slicing-a1.mass_integral-a1.lebesgue_deriv-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
