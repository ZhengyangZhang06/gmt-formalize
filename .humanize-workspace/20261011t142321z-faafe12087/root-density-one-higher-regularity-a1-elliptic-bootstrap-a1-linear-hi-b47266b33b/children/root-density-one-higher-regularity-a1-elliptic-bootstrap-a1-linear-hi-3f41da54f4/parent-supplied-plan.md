# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.differentiated_system-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-linear-hi-3f41da54f4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1`
- Child key: `differentiated_system`
- Declaration: `Submission.dohr_eb_lhr_differentiated_system`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (e : Rn n), IsOpen U → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U) → (∀ P : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => Φ x P) U) → ContDiffOn ℝ 2 v U → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, a x (fderiv ℝ v x) (fderiv ℝ ζ x) = ∫ x in U, Φ x (fderiv ℝ ζ x)) → ∃ Ψ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, (∀ x ∈ U, ∀ P : Rn n →L[ℝ] Rn ℓ, Ψ x P = fderiv ℝ (fun z => Φ z P) x e - fderiv ℝ (fun z => a z (fderiv ℝ v x) P) x e) ∧ ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, a x (fderiv ℝ (fun z => fderiv ℝ v z e) x) (fderiv ℝ ζ x) = ∫ x in U, Ψ x (fderiv ℝ ζ x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
