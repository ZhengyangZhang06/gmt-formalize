# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.imrep_mass_and_support-a1.smooth_unit_approximation-a1.continuous_unit_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-smooth-27a23e62de/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.smooth_unit_approximation-a1`
- Child key: `continuous_unit_extension`
- Declaration: `Submission.dor_ims_sua_continuous_unit_extension`
- Exact Lean type: `∀ (P n : ℕ) (K V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n), IsCompact K → IsOpen V → K ⊆ V → ContinuousOn β K → (∀ x ∈ K, covectorEuclideanNorm (β x) ≤ 1) → ∃ g : Euclid P → Covector (Euclid P) n, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ V ∧ (∀ x, covectorEuclideanNorm (g x) ≤ 1) ∧ ∀ x ∈ K, g x = β x`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.smooth_unit_approximation-a1.coeff_norm_rep-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.smooth_unit_approximation-a1.covector_finite_dimensional-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
