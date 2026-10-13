# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1.inner_holder-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-el-higher-e4e3ba4721/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1`
- Child key: `inner_holder`
- Declaration: `Submission.dohr_eb_ehs_inner_right_holder`
- Exact Lean type: `∀ (n ℓ m : ℕ) (α : ℝ) (U : Set (Rn n)) (g : Rn n → Rn ℓ) (w : Rn ℓ), IsOpen U → IsLocallyHolderCkα m α g U → ContDiffOn ℝ m (fun x => inner ℝ (g x) w) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m (fun z => inner ℝ (g z) w) x - iteratedFDeriv ℝ m (fun z => inner ℝ (g z) w) y‖ ≤ C * ‖x - y‖ ^ α`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
