# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.holder_succ_iff_fderiv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-holder-su-d401bf599b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1`
- Child key: `holder_succ_iff_fderiv`
- Declaration: `Submission.dohr_eb_holder_succ_iff_fderiv`
- Exact Lean type: `∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) (α : ℝ) (f : Rn n → E) (U : Set (Rn n)), IsOpen U → (((ContDiffOn ℝ (m + 1 : ℕ) f U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ (m + 1) f x - iteratedFDeriv ℝ (m + 1) f y‖ ≤ C * ‖x - y‖ ^ α) ↔ (ContDiffOn ℝ 1 f U ∧ ContDiffOn ℝ m (fderiv ℝ f) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m (fderiv ℝ f) x - iteratedFDeriv ℝ m (fderiv ℝ f) y‖ ≤ C * ‖x - y‖ ^ α)) ∧ ((ContDiffOn ℝ (m + 1 : ℕ) f U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ (m + 1) f x - iteratedFDeriv ℝ (m + 1) f y‖ ≤ C * ‖x - y‖ ^ α) ↔ (ContDiffOn ℝ 1 f U ∧ ∀ k : Fin n, ContDiffOn ℝ m (fun x => fderiv ℝ f x (EuclideanSpace.single k (1 : ℝ))) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m (fun z => fderiv ℝ f z (EuclideanSpace.single k (1 : ℝ))) x - iteratedFDeriv ℝ m (fun z => fderiv ℝ f z (EuclideanSpace.single k (1 : ℝ))) y‖ ≤ C * ‖x - y‖ ^ α)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
