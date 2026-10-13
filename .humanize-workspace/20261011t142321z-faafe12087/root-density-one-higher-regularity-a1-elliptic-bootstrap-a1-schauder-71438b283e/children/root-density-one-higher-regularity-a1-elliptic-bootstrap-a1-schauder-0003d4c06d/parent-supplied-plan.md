# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.holder_diag_subseq-a1.holder_of_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-0003d4c06d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.holder_diag_subseq-a1`
- Child key: `holder_of_limit`
- Declaration: `Submission.dohr_eb_sch_bu_hds_holder_of_limit`
- Exact Lean type: `∀ (n ℓ : ℕ) (α K : ℝ) (F : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ)) (V : Rn n → (Rn n →L[ℝ] Rn ℓ)), 0 < α → 0 ≤ K → (∀ z, Tendsto (fun j => F j z) atTop (𝓝 (V z))) → (∀ z z' : Rn n, ∀ᶠ j in atTop, ‖F j z - F j z'‖ ≤ K * ‖z - z'‖ ^ α) → (∀ z z' : Rn n, ‖V z - V z'‖ ≤ K * ‖z - z'‖ ^ α) ∧ Continuous V`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
