# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_graph_corollary-a1.hole_estimate-a1.hole_annulus_lower-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-hole-estimate-a1-hole-annulus-lower-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_graph_corollary-a1.hole_estimate-a1`
- Child key: `hole_annulus_lower`
- Declaration: `Submission.lgc_hole_annulus_lower`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (p : Amb n ℓ → (Amb n ℓ →L[ℝ] Amb n ℓ)) (ζ y : Amb n ℓ) (s ω c : ℝ), 0 < s → 0 < ω → AEStronglyMeasurable p μ → (∀ x, ‖p x‖ ≤ 1) → μ (closedBall ζ s) = 0 → μ (closedBall ζ (3 * s)) ≠ ⊤ → dist y ζ ≤ 2 * s → ENNReal.ofReal (ω * s ^ n / 2) ≤ μ (closedBall y s) → c ≤ ω / (4 * 3 ^ n) → ((3 * s) ^ n)⁻¹ * (μ (closedBall ζ (3 * s))).toReal ≤ Real.exp 2 * ((s ^ n)⁻¹ * (μ (closedBall ζ s)).toReal) + c + Real.exp 2 * ∫ x in closedBall ζ (3 * s) \ closedBall ζ s, ‖(x - ζ) - p x (x - ζ)‖ ^ 2 / ‖x - ζ‖ ^ (n + 2) ∂μ → s ^ (n + 2) ≤ 4 * 3 ^ n * Real.exp 2 / ω * ∫ x in closedBall ζ (3 * s), ‖(x - ζ) - p x (x - ζ)‖ ^ 2 ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
