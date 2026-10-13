# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_campanato-a1.lipschitz_ae_derivative-a1.line_integral_rep-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-lipschitz-ae-derivative-30a294660c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.graph_campanato-a1.lipschitz_ae_derivative-a1`
- Child key: `line_integral_rep`
- Declaration: `Submission.allard52_lad_line_integral_rep`
- Exact Lean type: `∀ (n ℓ : ℕ) (f : Rn n → Rn ℓ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (U : Set (Rn n)) (K : ℝ≥0), IsOpen U → Convex ℝ U → LipschitzOnWith K f U → ContinuousOn g U → (∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ U → HasFDerivAt f (g x) x) → ∀ x ∈ U, ∀ y ∈ U, f y - f x = ∫ τ in (0:ℝ)..1, g (x + τ • (y - x)) (y - x)`

## Sibling prerequisites

- `root.allard_regularity-a1.graph_campanato-a1.lipschitz_ae_derivative-a1.segment_null-a1`
- `root.allard_regularity-a1.graph_campanato-a1.lipschitz_ae_derivative-a1.lipschitz_ftc-a1`
- `root.allard_regularity-a1.graph_campanato-a1.lipschitz_ae_derivative-a1.segment_integral_continuous-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
