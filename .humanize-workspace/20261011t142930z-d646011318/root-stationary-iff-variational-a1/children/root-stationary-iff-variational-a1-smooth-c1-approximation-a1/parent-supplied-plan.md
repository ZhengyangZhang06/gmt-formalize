# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_iff_variational-a1.smooth_c1_approximation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-stationary-iff-variational-a1-smooth-c1-approximation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_iff_variational-a1`
- Child key: `smooth_c1_approximation`
- Declaration: `Submission.exists_smooth_approx_testField_fderiv`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Ambient n ℓ)) (X : Ambient n ℓ → Ambient n ℓ), IsOpen U → IsTestField U X → ∃ (K : Set (Ambient n ℓ)) (Y : ℕ → Ambient n ℓ → Ambient n ℓ), IsCompact K ∧ K ⊆ U ∧ tsupport X ⊆ K ∧ (∀ k, ContDiff ℝ ∞ (Y k) ∧ HasCompactSupport (Y k) ∧ tsupport (Y k) ⊆ K) ∧ TendstoUniformly (fun k ↦ fderiv ℝ (Y k)) (fderiv ℝ X) atTop`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
