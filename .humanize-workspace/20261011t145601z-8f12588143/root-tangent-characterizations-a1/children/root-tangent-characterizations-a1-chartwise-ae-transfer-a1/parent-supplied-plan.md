# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_characterizations-a1.chartwise_ae_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-tangent-characterizations-a1-chartwise-ae-transfer-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_characterizations-a1`
- Child key: `chartwise_ae_transfer`
- Declaration: `Submission.ae_of_ae_on_submanifold_charts`
- Exact Lean type: `∀ (n N : ℕ) (M N₀ : Set (Rn N)) (S : ℕ → Set (Rn N)) (Q : Rn N → Prop), μHE[n] N₀ = 0 → (∀ j, IsC1Submanifold n (S j)) → M ⊆ N₀ ∪ ⋃ j, S j → (∀ (V : Set (Rn n)) (ψ : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 1 ψ V → (∀ u ∈ V, Function.Injective (fderiv ℝ ψ u)) → ∀ᵐ u ∂(volume : Measure (Rn n)), u ∈ V → ψ u ∈ M → Q (ψ u)) → ∀ᵐ x ∂(μHE[n] : Measure (Rn N)), x ∈ M → Q x`

## Sibling prerequisites

- `root.tangent_characterizations-a1.null_image_locally_lipschitz-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
