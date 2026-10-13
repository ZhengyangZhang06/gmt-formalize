# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_graph_corollary-a1.hole_estimate-a1.hole_split_upper-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-hole-estimate-a1-hole-split-upper-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_graph_corollary-a1.hole_estimate-a1`
- Child key: `hole_split_upper`
- Declaration: `Submission.lgc_hole_split_upper`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (p : Amb n ℓ → (Amb n ℓ →L[ℝ] Amb n ℓ)) (T : Submodule ℝ (Amb n ℓ)) (F : Set (Amb n ℓ)) (ζ : Amb n ℓ) (s ε : ℝ), 0 < s → AEStronglyMeasurable p μ → (∀ x, ‖p x‖ ≤ 1) → MeasurableSet F → μ (closedBall ζ (3 * s)) ≠ ⊤ → (∀ x ∈ F, ‖(x - ζ) - T.starProjection (x - ζ)‖ ≤ ε * ‖x - ζ‖) → ∫ x in closedBall ζ (3 * s), ‖(x - ζ) - p x (x - ζ)‖ ^ 2 ∂μ ≤ 18 * s ^ 2 * (ε ^ 2 * (μ (closedBall ζ (3 * s))).toReal + (μ (closedBall ζ (3 * s) \ F)).toReal + ∫ x in closedBall ζ (3 * s), hsNormSq (p x - T.starProjection) ∂μ)`

## Sibling prerequisites

- `root.lipschitz_graph_corollary-a1.hole_estimate-a1.hs_norm_bounds-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
