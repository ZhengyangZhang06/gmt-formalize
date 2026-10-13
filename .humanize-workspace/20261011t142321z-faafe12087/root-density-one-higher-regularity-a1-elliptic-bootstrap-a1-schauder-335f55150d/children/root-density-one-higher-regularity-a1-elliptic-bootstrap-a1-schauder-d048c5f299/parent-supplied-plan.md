# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.weak_eq_limit-a1.pairing_uniform_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-d048c5f299/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.weak_eq_limit-a1`
- Child key: `pairing_uniform_limit`
- Declaration: `Submission.dohr_eb_sch_bu_wel_pairing_tendstoUniformlyOn`
- Exact Lean type: `∀ (n ℓ : ℕ) (α r Z N : ℝ) (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (ah : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Ψ : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (U : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ)) (V Q : Rn n → (Rn n →L[ℝ] Rn ℓ)) (K : Set (Rn n)) (c d : ℕ → ℝ), 0 ≤ α → Tendsto c atTop (𝓝 0) → Tendsto d atTop (𝓝 0) → TendstoUniformlyOn U V atTop K → (∀ z ∈ K, ‖z‖ ≤ r) → (∀ z ∈ K, ‖Q z‖ ≤ Z) → (∀ z ∈ K, ‖V z‖ ≤ N) → (∀ᶠ k in atTop, ∀ z ∈ K, ∀ P P' : Rn n →L[ℝ] Rn ℓ, |ah k z P P' - A P P'| ≤ c k * (1 + ‖z‖ ^ α) * ‖P‖ * ‖P'‖) → (∀ᶠ k in atTop, ∀ z ∈ K, ∀ P : Rn n →L[ℝ] Rn ℓ, |Ψ k z P| ≤ d k * ‖z‖ ^ α * ‖P‖) → TendstoUniformlyOn (fun k z => ah k z (U k z) (Q z)) (fun z => A (V z) (Q z)) atTop K ∧ TendstoUniformlyOn (fun k z => Ψ k z (Q z)) (fun _ => (0 : ℝ)) atTop K`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
