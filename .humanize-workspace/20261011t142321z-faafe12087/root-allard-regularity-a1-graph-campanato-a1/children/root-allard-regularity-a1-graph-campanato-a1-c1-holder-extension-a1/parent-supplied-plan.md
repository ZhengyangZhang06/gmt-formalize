# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_campanato-a1.c1_holder_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-c1-holder-extension-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.graph_campanato-a1`
- Child key: `c1_holder_extension`
- Declaration: `Submission.allard52_c1_holder_of_ae_fderiv`
- Exact Lean type: `∀ (n ℓ : ℕ) (f : Rn n → Rn ℓ) (c : Rn n) (r : ℝ) (K : ℝ≥0) (Z : Set (Rn n)) (M R α : ℝ), 0 ≤ M → 0 < R → 0 < α → LipschitzOnWith K f (ball c r) → Z ⊆ ball c r → volume (ball c r \ Z) = 0 → (∀ x ∈ Z, DifferentiableAt ℝ f x) → (∀ x ∈ Z, ∀ y ∈ Z, hsNorm (fderiv ℝ f x - fderiv ℝ f y) ≤ M * (‖x - y‖ / R) ^ α) → ContDiffOn ℝ 1 f (ball c r) ∧ ∀ x ∈ ball c r, ∀ y ∈ ball c r, hsNorm (fderiv ℝ f x - fderiv ℝ f y) ≤ M * (‖x - y‖ / R) ^ α`

## Sibling prerequisites

- `root.allard_regularity-a1.graph_campanato-a1.lipschitz_ae_derivative-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
