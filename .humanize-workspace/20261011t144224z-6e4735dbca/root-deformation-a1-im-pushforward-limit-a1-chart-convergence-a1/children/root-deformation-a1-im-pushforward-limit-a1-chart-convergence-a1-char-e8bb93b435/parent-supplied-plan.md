# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.chart_orientation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1-char-e8bb93b435/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1`
- Child key: `chart_orientation`
- Declaration: `Submission.deformation_ipl_cc_chart_orientation_sign`
- Exact Lean type: `∀ (P k : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k) (Φ : Eucl k → Eucl P) (Ω : Set (Eucl k)), IsOpen U → IsRectifiableTriple U k M θ ξ → IsOpen Ω → ContDiff ℝ 1 Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∃ σ : Eucl k → ℝ, AEStronglyMeasurable σ ((volume : Measure (Eucl k)).restrict (Ω ∩ Φ ⁻¹' M)) ∧ ∀ᵐ w ∂((volume : Measure (Eucl k)).restrict (Ω ∩ Φ ⁻¹' M)), (σ w = 1 ∨ σ w = -1) ∧ Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det • ξ (Φ w) = σ w • simpleNVector (fun b => fderiv ℝ Φ w (EuclideanSpace.single b 1))`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.simple_nvector_algebra-a1`
- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1`
- `root.lipschitz_pushforward_im-a1.chart_chain_rule-a1.ae_pullback-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
