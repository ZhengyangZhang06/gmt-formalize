# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.rescale-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-07004ffedb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1`
- Child key: `rescale`
- Declaration: `Submission.dohr_eb_sch_weak_eq_affine_rescale`
- Exact Lean type: `∀ (n ℓ : ℕ) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (w : Rn n → Rn ℓ) (U : Set (Rn n)) (y z₀ : Rn n) (ρ r : ℝ), 0 < ρ → IsOpen U → ball (y + ρ • z₀) (ρ * r) ⊆ U → ContDiffOn ℝ 1 w U → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, a x (fderiv ℝ w x) (fderiv ℝ ζ x) = ∫ x in U, Φ x (fderiv ℝ ζ x)) → ContDiffOn ℝ 1 (fun z => w (y + ρ • z)) (ball z₀ r) ∧ (∀ z ∈ ball z₀ r, fderiv ℝ (fun z => w (y + ρ • z)) z = ρ • fderiv ℝ w (y + ρ • z)) ∧ ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball z₀ r → ∫ z in ball z₀ r, a (y + ρ • z) (fderiv ℝ (fun z => w (y + ρ • z)) z) (fderiv ℝ ζ z) = ∫ z in ball z₀ r, (ρ • Φ (y + ρ • z)) (fderiv ℝ ζ z)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
