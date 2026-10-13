# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_campanato-a1.lipschitz_ae_derivative-a1.fderiv_of_line_integral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-lipschitz-ae-derivative-500689eea2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.graph_campanato-a1.lipschitz_ae_derivative-a1`
- Child key: `fderiv_of_line_integral`
- Declaration: `Submission.allard52_lad_hasFDerivAt_of_line_integral`
- Exact Lean type: `∀ (n ℓ : ℕ) (f : Rn n → Rn ℓ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (U : Set (Rn n)) (x : Rn n), IsOpen U → x ∈ U → ContinuousOn g U → (∀ y ∈ U, f y - f x = ∫ τ in (0:ℝ)..1, g (x + τ • (y - x)) (y - x)) → HasFDerivAt f (g x) x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
