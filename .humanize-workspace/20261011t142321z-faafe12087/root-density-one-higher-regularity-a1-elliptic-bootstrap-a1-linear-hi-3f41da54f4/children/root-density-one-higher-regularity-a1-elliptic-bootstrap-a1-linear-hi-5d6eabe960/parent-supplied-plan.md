# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.differentiated_system-a1.weak_eq_deriv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-linear-hi-5d6eabe960/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.differentiated_system-a1`
- Child key: `weak_eq_deriv`
- Declaration: `Submission.dohr_eb_lhr_ds_weak_eq_fderiv`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Rn n)) (ω₁ ω₂ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (e : Rn n), IsOpen U → ContDiffOn ℝ 1 ω₁ U → ContDiffOn ℝ 1 ω₂ U → (∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in U, ω₁ x (fderiv ℝ φ x) = ∫ x in U, ω₂ x (fderiv ℝ φ x)) → ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → IntegrableOn (fun x => fderiv ℝ ω₁ x e (fderiv ℝ ζ x)) U ∧ IntegrableOn (fun x => fderiv ℝ ω₂ x e (fderiv ℝ ζ x)) U ∧ ∫ x in U, fderiv ℝ ω₁ x e (fderiv ℝ ζ x) = ∫ x in U, fderiv ℝ ω₂ x e (fderiv ℝ ζ x)`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.differentiated_system-a1.translate_weak-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
