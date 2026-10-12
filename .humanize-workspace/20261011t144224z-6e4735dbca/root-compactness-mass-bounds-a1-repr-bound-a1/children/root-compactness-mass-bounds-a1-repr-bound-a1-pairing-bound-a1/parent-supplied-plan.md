# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_mass_bounds-a1.repr_bound-a1.pairing_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-repr-bound-a1-pairing-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_mass_bounds-a1.repr_bound-a1`
- Child key: `pairing_bound`
- Declaration: `Submission.cmb_rb_integral_coeff_pairing_bound`
- Exact Lean type: `∀ (P n : ℕ) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n) (K : Set (Eucl P)), MeasurableSet K → (∀ β : SimonMultiIndex n P, IntegrableOn (fun x => euclideanNVectorCoordinate (v x) β) K μ) → ∀ (θ : Eucl P → Covector (Eucl P) n) (D : ℝ), Continuous θ → (∀ x, x ∉ K → θ x = 0) → (∀ x, covectorEuclideanNorm (θ x) ≤ D) → Integrable (fun x => ∑ β : SimonMultiIndex n P, euclideanCovectorCoordinate (θ x) β * euclideanNVectorCoordinate (v x) β) μ ∧ |∫ x, ∑ β : SimonMultiIndex n P, euclideanCovectorCoordinate (θ x) β * euclideanNVectorCoordinate (v x) β ∂μ| ≤ D * ∑ β : SimonMultiIndex n P, ∫ x in K, |euclideanNVectorCoordinate (v x) β| ∂μ`

## Sibling prerequisites

- `root.compactness_mass_bounds-a1.repr_bound-a1.coord_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
