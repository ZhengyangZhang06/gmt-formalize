# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.holder_succ_iff_fderiv-a1.column_iterated_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-holder-su-0b85993074/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.holder_succ_iff_fderiv-a1`
- Child key: `column_iterated_bounds`
- Declaration: `Submission.dohr_eb_hsif_iteratedFDeriv_column_bounds`
- Exact Lean type: `∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) (g : Rn n → (Rn n →L[ℝ] E)) (U : Set (Rn n)), IsOpen U → ContDiffOn ℝ m g U → ∀ x ∈ U, ∀ y ∈ U, (∀ k : Fin n, ‖iteratedFDeriv ℝ m (fun z => g z (EuclideanSpace.single k (1 : ℝ))) x - iteratedFDeriv ℝ m (fun z => g z (EuclideanSpace.single k (1 : ℝ))) y‖ ≤ ‖iteratedFDeriv ℝ m g x - iteratedFDeriv ℝ m g y‖) ∧ ‖iteratedFDeriv ℝ m g x - iteratedFDeriv ℝ m g y‖ ≤ ∑ k : Fin n, ‖iteratedFDeriv ℝ m (fun z => g z (EuclideanSpace.single k (1 : ℝ))) x - iteratedFDeriv ℝ m (fun z => g z (EuclideanSpace.single k (1 : ℝ))) y‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
