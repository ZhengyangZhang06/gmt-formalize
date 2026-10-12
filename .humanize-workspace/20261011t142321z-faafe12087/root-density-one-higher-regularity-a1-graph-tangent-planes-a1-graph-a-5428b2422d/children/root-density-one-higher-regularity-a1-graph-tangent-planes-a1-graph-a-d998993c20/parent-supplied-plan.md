# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.graph_tangent_planes-a1.graph_approx_tangent-a1.setintegral_localize-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1-graph-a-d998993c20/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1.graph_approx_tangent-a1`
- Child key: `setintegral_localize`
- Declaration: `Submission.dohr_tp_gat_setIntegral_eq_of_inter`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (φ : Amb n ℓ → ℝ) (S T B : Set (Amb n ℓ)), MeasurableSet B → (∀ w, w ∉ B → φ w = 0) → S ∩ B ⊆ T → T ⊆ S → ∫ w in S, φ w ∂μ = ∫ w in T, φ w ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
