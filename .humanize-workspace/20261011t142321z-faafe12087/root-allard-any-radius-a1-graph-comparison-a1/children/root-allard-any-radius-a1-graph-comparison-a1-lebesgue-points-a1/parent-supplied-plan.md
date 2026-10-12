# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.graph_comparison-a1.lebesgue_points-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-comparison-a1-lebesgue-points-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.graph_comparison-a1`
- Child key: `lebesgue_points`
- Declaration: `Submission.anyrad_gc_hsNormSq_lebesgue_ae`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (O : Set (Amb n ℓ)), IsOpen O → μ O < ⊤ → ∀ (g : Amb n ℓ → (Amb n ℓ →L[ℝ] Amb n ℓ)) (C : ℝ), AEStronglyMeasurable g μ → (∀ w, ‖g w‖ ≤ C) → ∀ᵐ y ∂μ, y ∈ O → Tendsto (fun s : ℝ => (μ (closedBall y s))⁻¹ * ∫⁻ w in closedBall y s, ENNReal.ofReal (hsNormSq (g w - g y)) ∂μ) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
