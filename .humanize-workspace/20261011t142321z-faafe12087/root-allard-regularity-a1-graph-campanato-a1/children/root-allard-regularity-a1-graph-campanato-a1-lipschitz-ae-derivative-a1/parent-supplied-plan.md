# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_campanato-a1.lipschitz_ae_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-lipschitz-ae-derivative-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.graph_campanato-a1`
- Child key: `lipschitz_ae_derivative`
- Declaration: `Submission.allard52_lipschitz_hasFDerivAt_of_ae`
- Exact Lean type: `∀ (n ℓ : ℕ) (f : Rn n → Rn ℓ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (c : Rn n) (r : ℝ) (K : ℝ≥0), LipschitzOnWith K f (ball c r) → ContinuousOn g (ball c r) → (∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball c r → HasFDerivAt f (g x) x) → ∀ x ∈ ball c r, HasFDerivAt f (g x) x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
