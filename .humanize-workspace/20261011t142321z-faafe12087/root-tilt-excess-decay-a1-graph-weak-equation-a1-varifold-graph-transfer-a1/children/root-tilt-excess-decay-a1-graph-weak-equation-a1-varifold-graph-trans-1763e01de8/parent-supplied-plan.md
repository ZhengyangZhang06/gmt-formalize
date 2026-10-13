# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.varifold_graph_transfer-a1.transfer_consequences-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-varifold-graph-trans-1763e01de8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.varifold_graph_transfer-a1`
- Child key: `transfer_consequences`
- Declaration: `Submission.gwe_vgt_transfer_consequences`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (S : Set (Amb n ℓ)) (A : Set (Rn n)) (G : Rn n → Amb n ℓ) (W : Rn n → ℝ), MeasurableSet A → Measurable G → Measurable W → (∀ x, 0 ≤ W x) → (∀ φ : Amb n ℓ → ℝ≥0∞, Measurable φ → ∫⁻ y in S, φ y ∂μ = ∫⁻ x in A, ENNReal.ofReal (W x) * φ (G x)) → (∀ φ : Amb n ℓ → ℝ, Measurable φ → ∫ y in S, φ y ∂μ = ∫ x in A, W x * φ (G x)) ∧ ∀ Z : Set (Amb n ℓ), μ Z = 0 → ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ A → G x ∈ Z → W x = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
