# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.difference_quotient_limit-a1.c1holder_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-differenc-55008b8691/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.difference_quotient_limit-a1`
- Child key: `c1holder_limit`
- Declaration: `Submission.dohr_eb_dql_c1Holder_of_tendstoUniformlyOn`
- Exact Lean type: `∀ (n ℓ : ℕ) (ι : Type) (l : Filter ι), l.NeBot → ∀ (F : ι → Rn n → Rn ℓ) (G : Rn n → Rn ℓ) (x₀ : Rn n) (ρ α M : ℝ), 0 < α → (∀ᶠ i in l, ∀ x ∈ ball x₀ ρ, DifferentiableAt ℝ (F i) x) → (∀ᶠ i in l, ∀ x ∈ ball x₀ ρ, ‖fderiv ℝ (F i) x‖ ≤ M) → (∀ᶠ i in l, ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖fderiv ℝ (F i) x - fderiv ℝ (F i) y‖ ≤ M * ‖x - y‖ ^ α) → (∀ K : Set (Rn n), IsCompact K → K ⊆ ball x₀ ρ → TendstoUniformlyOn F G l K) → ContDiffOn ℝ 1 G (ball x₀ ρ) ∧ (∀ x ∈ ball x₀ ρ, ‖fderiv ℝ G x‖ ≤ M) ∧ ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ M * ‖x - y‖ ^ α`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.difference_quotient_limit-a1.interpolation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
