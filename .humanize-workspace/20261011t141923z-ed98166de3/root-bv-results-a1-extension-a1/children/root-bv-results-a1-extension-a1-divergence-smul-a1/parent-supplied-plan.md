# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.bv_results-a1.extension-a1.divergence_smul-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-extension-a1-divergence-smul-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.bv_results-a1.extension-a1`
- Child key: `divergence_smul`
- Declaration: `Submission.bv_ext_euclideanDivergence_smul`
- Exact Lean type: `∀ (n : ℕ) (φ : Rn n → ℝ) (g : Rn n → Rn n) (x : Rn n), DifferentiableAt ℝ φ x → DifferentiableAt ℝ g x → Chapter02.euclideanDivergence (fun y ↦ φ y • g y) x = φ x * Chapter02.euclideanDivergence g x + fderiv ℝ φ x (g x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
