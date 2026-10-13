# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.holder_diag_subseq-a1.compact_subseq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-85c2302449/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.holder_diag_subseq-a1`
- Child key: `compact_subseq`
- Declaration: `Submission.dohr_eb_sch_bu_hds_compact_subseq`
- Exact Lean type: `∀ (n ℓ : ℕ) (α K M : ℝ) (S : Set (Rn n)) (g : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ)), 0 < α → 0 ≤ K → IsCompact S → (∀ j, ∀ z ∈ S, ‖g j z‖ ≤ M) → (∀ j, ∀ z ∈ S, ∀ z' ∈ S, ‖g j z - g j z'‖ ≤ K * ‖z - z'‖ ^ α) → ∃ (χ : ℕ → ℕ) (G : Rn n → (Rn n →L[ℝ] Rn ℓ)), StrictMono χ ∧ TendstoUniformlyOn (fun j => g (χ j)) G atTop S`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.holder_diag_subseq-a1.diagonal_extract-a1`
- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.holder_diag_subseq-a1.unif_of_dense-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
