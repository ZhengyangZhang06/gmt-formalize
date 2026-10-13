# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.radius-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-03b7966d86/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1`
- Child key: `radius`
- Declaration: `Submission.cbrld_exists_good_slice_radius`
- Exact Lean type: `∀ (P n : ℕ) (μ : Measure (Euclid P)) (x₁ : Euclid P) (a s : ℝ) (N : Set ℝ), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → 1 ≤ n → 0 < a → 0 < s → μ (ball x₁ s) < ENNReal.ofReal ((a * s) ^ n) → volume N = 0 → ∃ ρ : ℝ, 0 < ρ ∧ ρ < s ∧ ρ ∉ N ∧ μ (sphere x₁ ρ) = 0 ∧ liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | ρ - h < dist x x₁ ∧ dist x x₁ < ρ}) (𝓝[>] 0) ≤ ENNReal.ofReal (2 * n * a * (μ (ball x₁ ρ)).toReal ^ (((n : ℝ) - 1) / n))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
