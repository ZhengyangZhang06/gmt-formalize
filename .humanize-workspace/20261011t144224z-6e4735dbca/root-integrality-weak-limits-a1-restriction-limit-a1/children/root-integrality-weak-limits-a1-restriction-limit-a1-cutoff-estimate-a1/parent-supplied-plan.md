# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.restriction_limit-a1.cutoff_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-restriction-limit-a1-cutoff-estimate-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.restriction_limit-a1`
- Child key: `cutoff_estimate`
- Declaration: `Submission.iwl_rl_restriction_cutoff_estimate`
- Exact Lean type: `∀ (P k : ℕ) (U W : Set (Eucl P)) (φ : Eucl P → ℝ) (a s c : ℝ) (Y S : GeometricCurrentOn U k) (μ : Measure (Eucl P)) (ω ω' : TestFormOn U k), IsOpen W → W ⊆ U → ContinuousOn φ U → a < s → IsRestriction Y {x | x ∈ U ∧ φ x < s} S → (∀ (A : Set (Eucl P)) (S' : GeometricCurrentOn U k), IsRestriction Y A S' → ∀ W' : Set (Eucl P), IsOpen W' → W' ⊆ U → S'.massOn W' = μ (W' ∩ A)) → Y.massOn W < ∞ → (∀ x ∈ U, s ≤ φ x → (ω' : DifferentialForm (Eucl P) k) x = 0) → tsupport ((ω : DifferentialForm (Eucl P) k) - (ω' : DifferentialForm (Eucl P) k)) ⊆ {x | x ∈ W ∧ a < φ x} → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) k) x - (ω' : DifferentialForm (Eucl P) k) x) ≤ c) → |S ω - Y ω'| ≤ c * ((Y.massOn {x | x ∈ W ∧ φ x < s}).toReal - (Y.massOn {x | x ∈ W ∧ φ x < a}).toReal)`

## Sibling prerequisites

- `root.compactness_mass_bounds-a1.mass_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
