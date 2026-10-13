# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.differentiated_system-a1.translate_weak-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-linear-hi-55e76f25eb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.differentiated_system-a1`
- Child key: `translate_weak`
- Declaration: `Submission.dohr_eb_lhr_ds_translate_weak_eq`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Rn n)) (ω₁ ω₂ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (e : Rn n) (s : ℝ) (ζ : Rn n → Rn ℓ), (∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in U, ω₁ x (fderiv ℝ φ x) = ∫ x in U, ω₂ x (fderiv ℝ φ x)) → ContDiff ℝ 1 ζ → HasCompactSupport ζ → (∀ y ∈ tsupport ζ, y + s • e ∈ U) → ∫ y, ω₁ (y + s • e) (fderiv ℝ ζ y) = ∫ y, ω₂ (y + s • e) (fderiv ℝ ζ y)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
