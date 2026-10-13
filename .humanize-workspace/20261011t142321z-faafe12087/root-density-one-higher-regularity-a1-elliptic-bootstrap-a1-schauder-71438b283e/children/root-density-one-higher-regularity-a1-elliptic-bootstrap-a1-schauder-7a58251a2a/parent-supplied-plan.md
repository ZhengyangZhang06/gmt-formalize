# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.holder_diag_subseq-a1.unif_of_dense-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-7a58251a2a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.holder_diag_subseq-a1`
- Child key: `unif_of_dense`
- Declaration: `Submission.dohr_eb_sch_bu_hds_unif_of_dense`
- Exact Lean type: `∀ (n ℓ : ℕ) (α K : ℝ) (S D : Set (Rn n)) (F : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ)), 0 < α → 0 ≤ K → IsCompact S → D ⊆ S → S ⊆ closure D → (∀ d ∈ D, ∃ v : Rn n →L[ℝ] Rn ℓ, Tendsto (fun j => F j d) atTop (𝓝 v)) → (∀ j, ∀ z ∈ S, ∀ z' ∈ S, ‖F j z - F j z'‖ ≤ K * ‖z - z'‖ ^ α) → ∃ G : Rn n → (Rn n →L[ℝ] Rn ℓ), TendstoUniformlyOn F G atTop S`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
