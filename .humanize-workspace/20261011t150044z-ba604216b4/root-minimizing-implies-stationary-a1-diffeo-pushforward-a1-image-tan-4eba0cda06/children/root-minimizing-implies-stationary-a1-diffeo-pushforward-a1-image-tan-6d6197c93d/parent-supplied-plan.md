# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_tangent_transport-a1.ae_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-tan-6d6197c93d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_tangent_transport-a1`
- Child key: `ae_transfer`
- Declaration: `Submission.dpf_itt_ae_of_ae_pieces`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (F : ℕ → Euclid n → Euclid P) (B : ℕ → Set (Euclid n)) (p : Euclid P → Prop), MeasurableSet M → (∀ i, ∃ L : NNReal, LipschitzWith L (F i)) → μHE[n] (M \ ⋃ i, F i '' B i) = 0 → (∀ i, ∀ᵐ b ∂(volume.restrict (B i)), p (F i b)) → ∀ᵐ x ∂(μHE[n].restrict M), p x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
