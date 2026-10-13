# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.dq_uniform_bounds-a1.fderiv_consts-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-linear-hi-a39c328641/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.dq_uniform_bounds-a1`
- Child key: `fderiv_consts`
- Declaration: `Submission.dohr_eb_lhr_dqub_fderiv_consts`
- Exact Lean type: `∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ) (U K : Set E) (g : E → F), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 1 g U → (∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 g x - iteratedFDeriv ℝ 1 g y‖ ≤ C * ‖x - y‖ ^ α) → ∃ S H : ℝ, 0 ≤ S ∧ 0 ≤ H ∧ (∀ x ∈ K, ‖fderiv ℝ g x‖ ≤ S) ∧ ∀ x ∈ K, ∀ y ∈ K, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ H * ‖x - y‖ ^ α`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
