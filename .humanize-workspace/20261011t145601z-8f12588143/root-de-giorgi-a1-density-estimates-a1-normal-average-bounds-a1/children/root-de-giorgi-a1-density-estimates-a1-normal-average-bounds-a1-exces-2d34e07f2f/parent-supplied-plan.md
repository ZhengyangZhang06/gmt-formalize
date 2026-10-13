# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.density_estimates-a1.normal_average_bounds-a1.excess_cauchy_schwarz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-normal-average-bounds-a1-exces-2d34e07f2f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.density_estimates-a1.normal_average_bounds-a1`
- Child key: `excess_cauchy_schwarz`
- Declaration: `Submission.deGiorgiNAB_excess_le_sqrt`
- Exact Lean type: `∀ (N : ℕ) (μ : Measure (Rn N)) (ν : Rn N → Rn N) (e : Rn N) (S : Set (Rn N)), μ S < ∞ → AEStronglyMeasurable ν μ → (∀ᵐ y ∂μ, ‖ν y‖ = 1) → ‖e‖ = 1 → ∫ y in S, ‖ν y - e‖ ∂μ ≤ (μ S).toReal * Real.sqrt (2 * (1 - (μ S).toReal⁻¹ * ∫ y in S, inner ℝ (ν y) e ∂μ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
