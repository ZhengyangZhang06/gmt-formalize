# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tangential_estimate-a1.localized_comparison-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-graph-tangential-est-14953ad692/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tangential_estimate-a1`
- Child key: `localized_comparison`
- Declaration: `Submission.gte_localized_comparison`
- Exact Lean type: `∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (B B' G G' : Set X) (Φ φ ψ : X → ℝ) (M : ℝ) (m : ℝ≥0∞), 0 ≤ M → MeasurableSet G → MeasurableSet G' → G' ⊆ B → G' ⊆ B' → IntegrableOn Φ B μ → (∀ x, |Φ x| ≤ M) → (∀ x ∈ (B \ G') ∩ G, Φ x = 0) → μ ((B \ G') \ G) ≤ m → m < ⊤ → AEStronglyMeasurable φ (μ.restrict G') → IntegrableOn ψ B' μ → (∀ x, 0 ≤ ψ x) → (∀ᵐ x ∂μ, x ∈ G' → |Φ x - φ x| ≤ M * ψ x) → |∫ x in G', φ x ∂μ| ≤ |∫ x in B, Φ x ∂μ| + M * m.toReal + M * ∫ x in B', ψ x ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
