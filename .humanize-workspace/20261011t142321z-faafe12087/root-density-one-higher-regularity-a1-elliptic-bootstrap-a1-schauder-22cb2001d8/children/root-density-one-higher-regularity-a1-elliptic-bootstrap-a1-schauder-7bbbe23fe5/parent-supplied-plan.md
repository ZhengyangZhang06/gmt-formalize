# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.weak_eq_sub_affine-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-7bbbe23fe5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1`
- Child key: `weak_eq_sub_affine`
- Declaration: `Submission.dohr_eb_sch_bu_weak_eq_sub_affine`
- Exact Lean type: `∀ (n ℓ : ℕ) (b : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Θ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (D : Set (Rn n)) (B₀ : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Θ₀ : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (P₀ : Rn n →L[ℝ] Rn ℓ) (c : Rn ℓ) (s : ℝ), IsOpen D → ContinuousOn (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) => b p.1 p.2.1 p.2.2) (D ×ˢ univ) → ContinuousOn Θ D → ContDiffOn ℝ 1 v D → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ D → ∫ x in D, b x (fderiv ℝ v x) (fderiv ℝ ζ x) = ∫ x in D, Θ x (fderiv ℝ ζ x)) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, B₀ P₀ (fderiv ℝ ζ x) = 0) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, Θ₀ (fderiv ℝ ζ x) = 0) → ContDiffOn ℝ 1 (fun x => s • (v x - c - P₀ x)) D ∧ (∀ x ∈ D, fderiv ℝ (fun x => s • (v x - c - P₀ x)) x = s • (fderiv ℝ v x - P₀)) ∧ ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ D → ∫ x in D, b x (fderiv ℝ (fun x => s • (v x - c - P₀ x)) x) (fderiv ℝ ζ x) = ∫ x in D, (s • ((Θ x - Θ₀) - (b x P₀ - B₀ P₀))) (fderiv ℝ ζ x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
