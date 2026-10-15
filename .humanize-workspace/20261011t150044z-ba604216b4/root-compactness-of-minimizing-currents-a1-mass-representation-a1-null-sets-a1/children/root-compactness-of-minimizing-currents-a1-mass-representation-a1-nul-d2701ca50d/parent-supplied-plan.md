# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.null_sets-a1.div_mass_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-nul-d2701ca50d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.null_sets-a1`
- Child key: `div_mass_bound`
- Declaration: `Submission.cmr_abs_integral_div_le_mass`
- Exact Lean type: `∀ (P m : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U (m + 1)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (m + 1)) (θ : Covector (Euclid P) (m + 1)) (b D : Euclid P → ℝ) (η : DifferentialForm (Euclid P) m) (ζ : DifferentialForm (Euclid P) (m + 1)) (K : ℝ), W ⊆ U → T.massOn W ≠ ∞ → T.boundary.massOn W ≠ ∞ → (∀ ω : TestFormOn U (m + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μ) → (∀ (k : ℕ) (S : GeometricCurrentOn U k) (ω : TestFormOn U k) (r : ℝ), S.massOn W ≠ ∞ → tsupport (ω : DifferentialForm (Euclid P) k) ⊆ W → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ r) → |S ω| ≤ r * (S.massOn W).toReal) → tsupport b ⊆ W → IsTestForm η → IsTestForm ζ → tsupport η ⊆ tsupport b → tsupport ζ ⊆ tsupport b → (∀ x, covectorEuclideanNorm (η x) ≤ K) → (∀ x, covectorEuclideanNorm (ζ x) ≤ K) → (∀ x, exteriorDerivative η x = (b x * D x) • θ + ζ x) → |∫ x, b x * ξ x θ * D x ∂(μ.restrict W)| ≤ K * ((T.boundary.massOn W).toReal + (T.massOn W).toReal)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
