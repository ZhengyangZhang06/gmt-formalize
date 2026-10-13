# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-22cb2001d8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1`
- Child key: `blowup_estimate`
- Declaration: `Submission.dohr_eb_sch_blowup_holder_estimate`
- Exact Lean type: `∀ n ℓ : ℕ, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 → ∀ lam M δ : ℝ, 0 < lam → 0 < δ → ∃ Cδ : ℝ, 0 ≤ Cδ ∧ ∀ (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (w : Rn n → Rn ℓ) (K S G : ℝ), 0 ≤ G → (∀ x ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ a x P P) → (∀ x ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q| ≤ M * ‖P‖ * ‖Q‖) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q - a y P Q| ≤ M * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, |Φ x P - Φ y P| ≤ G * ‖x - y‖ ^ α * ‖P‖) → (∀ x ∈ ball (0 : Rn n) 1, ‖w x‖ ≤ S) → ContDiffOn ℝ 1 w (ball (0 : Rn n) 1) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ K * ‖x - y‖ ^ α) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Rn n) 1 → ∫ x in ball (0 : Rn n) 1, a x (fderiv ℝ w x) (fderiv ℝ ζ x) = ∫ x in ball (0 : Rn n) 1, Φ x (fderiv ℝ ζ x)) → ∀ x ∈ ball (0 : Rn n) (1 / 2), ∀ y ∈ ball (0 : Rn n) (1 / 2), ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ (δ * K + Cδ * (S + G)) * ‖x - y‖ ^ α`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.zero_mean-a1`
- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.interpolation-a1`
- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.rescale-a1`
- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.liouville-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
