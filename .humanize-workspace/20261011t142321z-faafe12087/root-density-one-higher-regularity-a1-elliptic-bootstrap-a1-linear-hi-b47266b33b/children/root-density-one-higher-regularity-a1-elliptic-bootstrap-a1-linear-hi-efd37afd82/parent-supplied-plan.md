# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.holder_loc_sub_sum-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-linear-hi-efd37afd82/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1`
- Child key: `holder_loc_sub_sum`
- Declaration: `Submission.dohr_eb_lhr_holder_loc_sub_sum`
- Exact Lean type: `∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (j N : ℕ) (α : ℝ) (U : Set (Rn n)) (h g : Rn n → E) (f : Fin N → Rn n → E), IsOpen U → ContDiffOn ℝ j h U → (∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ j h x - iteratedFDeriv ℝ j h y‖ ≤ C * ‖x - y‖ ^ α) → (∀ i : Fin N, ContDiffOn ℝ j (f i) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ j (f i) x - iteratedFDeriv ℝ j (f i) y‖ ≤ C * ‖x - y‖ ^ α) → (∀ x ∈ U, g x = h x - ∑ i, f i x) → ContDiffOn ℝ j g U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ j g x - iteratedFDeriv ℝ j g y‖ ≤ C * ‖x - y‖ ^ α`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
