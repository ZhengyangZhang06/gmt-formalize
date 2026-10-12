# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.graph_tangent_planes-a1.lebesgue_point_growth-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1-lebesgu-aec964ab82/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1`
- Child key: `lebesgue_point_growth`
- Declaration: `Submission.dohr_tp_ae_lebesgue_point_of_growth`
- Exact Lean type: `∀ (n ℓ : ℕ) (ν : Measure (Amb n ℓ)) (f : Amb n ℓ → ℝ) (C : ℝ), Integrable f ν → (∀ (z : Amb n ℓ) (r : ℝ), 0 < r → ν (closedBall z r) ≤ ENNReal.ofReal (C * r ^ n)) → ∀ᵐ y ∂ν, Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ n)⁻¹) * ∫⁻ w in closedBall y r, ‖f w - f y‖ₑ ∂ν) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
