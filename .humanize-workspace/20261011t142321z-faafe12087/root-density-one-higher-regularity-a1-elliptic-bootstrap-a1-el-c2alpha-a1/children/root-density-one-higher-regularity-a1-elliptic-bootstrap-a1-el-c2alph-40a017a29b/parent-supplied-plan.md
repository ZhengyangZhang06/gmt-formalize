# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1.local_to_global_holder-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-el-c2alph-40a017a29b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1`
- Child key: `local_to_global_holder`
- Declaration: `Submission.dohr_eb_elc2_local_to_global_holder`
- Exact Lean type: `∀ (n ℓ : ℕ) (α : ℝ) (f : Rn n → Rn ℓ) (U : Set (Rn n)), 0 < α → IsOpen U → (∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ ContDiffOn ℝ 1 f (ball x r) ∧ ∃ C : ℝ, ∀ y ∈ ball x r, ∀ z ∈ ball x r, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ C * ‖y - z‖ ^ α) → IsLocallyHolderCkα 1 α f U`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
