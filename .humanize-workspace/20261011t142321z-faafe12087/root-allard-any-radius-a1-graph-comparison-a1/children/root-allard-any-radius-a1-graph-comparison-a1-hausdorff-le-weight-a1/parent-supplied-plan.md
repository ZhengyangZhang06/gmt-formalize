# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.graph_comparison-a1.hausdorff_le_weight-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-comparison-a1-hausdorff-le-weight-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.graph_comparison-a1`
- Child key: `hausdorff_le_weight`
- Declaration: `Submission.anyrad_gc_hausdorff_restrict_le_weight`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (O Γ : Set (Amb n ℓ)), IsOpen O → V.weight O < ⊤ → Γ ⊆ O → (∀ᵐ x ∂V.weight, 1 ≤ V.mult x) → (∀ y ∈ Γ, ∃ c s₀ : ℝ, 0 < c ∧ 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ → ENNReal.ofReal (c * s ^ n) ≤ V.weight (closedBall y s)) → (μHE[n] : Measure (Amb n ℓ)).restrict Γ ≤ V.weight`

## Sibling prerequisites

- `root.tilt_excess_height_estimate-a1.ae_tangent_planes-a1.upper_density_zero-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
