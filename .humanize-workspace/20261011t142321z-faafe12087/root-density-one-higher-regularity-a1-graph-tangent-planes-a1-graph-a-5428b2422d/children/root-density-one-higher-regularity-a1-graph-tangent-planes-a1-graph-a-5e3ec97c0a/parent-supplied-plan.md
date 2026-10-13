# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.graph_tangent_planes-a1.graph_approx_tangent-a1.blowup_two_point-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1-graph-a-5e3ec97c0a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1.graph_approx_tangent-a1`
- Child key: `blowup_two_point`
- Declaration: `Submission.dohr_tp_gat_blowup_two_point`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Rn n)) (G : Rn n → Amb n ℓ) (x : Rn n) (ρ ε : ℝ), IsOpen U → ContDiffOn ℝ 1 G U → x ∈ U → 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ v ∈ closedBall (0 : Rn n) ρ, x + t • v ∈ U) ∧ ∀ v ∈ closedBall (0 : Rn n) ρ, ∀ v' ∈ closedBall (0 : Rn n) ρ, ‖t⁻¹ • (G (x + t • v) - G (x + t • v')) - fderiv ℝ G x (v - v')‖ ≤ ε * ‖v - v'‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
