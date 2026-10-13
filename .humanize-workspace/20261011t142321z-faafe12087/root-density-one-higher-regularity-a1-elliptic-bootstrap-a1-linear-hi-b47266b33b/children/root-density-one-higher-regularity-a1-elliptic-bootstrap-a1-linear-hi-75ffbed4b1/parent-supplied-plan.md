# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.cover_holder_one-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-linear-hi-75ffbed4b1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1`
- Child key: `cover_holder_one`
- Declaration: `Submission.dohr_eb_lhr_cover_holder_one`
- Exact Lean type: `∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) (U : Set (Rn n)) (F : Rn n → E), 0 < α → IsOpen U → (∀ x ∈ U, ∃ R : ℝ, 0 < R ∧ ball x R ⊆ U ∧ ContDiffOn ℝ 1 F (ball x R) ∧ ∃ C : ℝ, ∀ y ∈ ball x R, ∀ z ∈ ball x R, ‖fderiv ℝ F y - fderiv ℝ F z‖ ≤ C * ‖y - z‖ ^ α) → ContDiffOn ℝ 1 F U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 F x - iteratedFDeriv ℝ 1 F y‖ ≤ C * ‖x - y‖ ^ α`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
