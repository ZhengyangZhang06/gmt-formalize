# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.radius-a1.annulus_liminf-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-c79dbf19c5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.radius-a1`
- Child key: `annulus_liminf`
- Declaration: `Submission.cbrld_radius_liminf_annulus_le_of_hasDerivAt`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (x₁ : Euclid P) (ρ d : ℝ), μ (ball x₁ ρ) ≠ ∞ → HasDerivAt (fun r : ℝ => (μ (ball x₁ r)).toReal) d ρ → liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | ρ - h < dist x x₁ ∧ dist x x₁ < ρ}) (𝓝[>] 0) ≤ ENNReal.ofReal d`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
