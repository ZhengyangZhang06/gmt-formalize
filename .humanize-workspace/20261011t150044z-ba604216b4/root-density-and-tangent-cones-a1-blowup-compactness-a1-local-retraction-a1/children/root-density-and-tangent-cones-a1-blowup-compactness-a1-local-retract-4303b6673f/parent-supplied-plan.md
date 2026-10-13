# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_retraction-a1.chart_image_nhds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-retract-4303b6673f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_retraction-a1`
- Child key: `chart_image_nhds`
- Declaration: `Submission.dtc_bc_lr_chart_image_nhds`
- Exact Lean type: `∀ (P d : ℕ) (N W : Set (Euclid P)) (V V₀ : Set (Euclid d)) (ψ : Euclid d → Euclid P) (v₀ : Euclid d), IsOpen W → ContinuousOn ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → IsOpen V₀ → V₀ ⊆ V → v₀ ∈ V₀ → ∃ ρ : ℝ, 0 < ρ ∧ N ∩ ball (ψ v₀) ρ ⊆ ψ '' V₀`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
