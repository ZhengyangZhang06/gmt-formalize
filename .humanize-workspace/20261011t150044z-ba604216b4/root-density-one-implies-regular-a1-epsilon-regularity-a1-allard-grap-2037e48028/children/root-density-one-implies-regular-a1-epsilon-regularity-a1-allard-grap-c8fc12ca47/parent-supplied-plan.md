# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_variation-a1.split_integral_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-c8fc12ca47/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_variation-a1`
- Child key: `split_integral_estimate`
- Declaration: `Submission.dorag_tes_gv_split_integral_estimate`
- Exact Lean type: `∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (A B F : Set X) (u g t : X → ℝ) (G : ℝ) (C : ℝ≥0∞), MeasurableSet A → MeasurableSet B → MeasurableSet F → A ⊆ B → 0 ≤ G → IntegrableOn u B μ → ENNReal.ofReal |∫ x in B, u x ∂μ| ≤ C → (∀ᵐ x ∂μ, x ∈ B → |u x| ≤ G) → (∀ᵐ x ∂μ, x ∈ B → x ∉ A → x ∈ F → u x = 0) → (∀ᵐ x ∂μ, x ∈ A → |u x - g x| ≤ G * t x) → ENNReal.ofReal |∫ x in A, g x ∂μ| ≤ ENNReal.ofReal G * (∫⁻ x in B, ENNReal.ofReal (t x) ∂μ + μ (B \ F)) + C`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
