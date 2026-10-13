# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.mass_representation-a1.continuous_mass_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1-continuous-mass-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.mass_representation-a1`
- Child key: `continuous_mass_bound`
- Declaration: `Submission.smr_ofReal_integral_le_massOn`
- Exact Lean type: `∀ (P k : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k), (∀ ω : TestFormOn U k, Integrable (fun x => v x ((ω : DifferentialForm (Eucl P) k) x)) μ) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) → ∀ (A : Set (Eucl P)) (S : GeometricCurrentOn U k), (∀ ω : TestFormOn U k, S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ) → ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → ∀ φ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ W → (∀ x, covectorEuclideanNorm (φ x) ≤ 1) → ENNReal.ofReal (∫ x in A, v x (φ x) ∂μ) ≤ S.massOn W`

## Sibling prerequisites

- `root.slicing-a1.mass_representation-a1.covector_isometry-a1`
- `root.slicing-a1.mass_representation-a1.testform_approx-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
