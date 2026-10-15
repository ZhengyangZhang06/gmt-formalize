# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.localize-a1.good_radius-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-b4bb58c8c4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.localize-a1`
- Child key: `good_radius`
- Declaration: `Submission.dtc_bc_lc_fd_lz_good_radius`
- Exact Lean type: `∀ (P : ℕ) (μ : ℕ → Measure (Euclid P)) (r₀ : ℝ) (Λ₀ : NNReal), (∀ (j : ℕ) (r : ℝ), μ j (ball (0 : Euclid P) r) < ∞) → (∀ j, μ j (ball (0 : Euclid P) (r₀ + 1)) ≤ (Λ₀ : ℝ≥0∞)) → ∃ t₀ ∈ Ioo r₀ (r₀ + 1), ∃ (φ : ℕ → ℕ) (C : NNReal), StrictMono φ ∧ ∀ j, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (φ j) {x : Euclid P | t₀ - h < ‖x‖ ∧ ‖x‖ < t₀}) (𝓝[>] 0) ≤ (C : ℝ≥0∞)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.localize-a1.dini_measurable-a1`
- `root.compactness_of_minimizing_currents-a1.slicing-a1.mass_integral-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
