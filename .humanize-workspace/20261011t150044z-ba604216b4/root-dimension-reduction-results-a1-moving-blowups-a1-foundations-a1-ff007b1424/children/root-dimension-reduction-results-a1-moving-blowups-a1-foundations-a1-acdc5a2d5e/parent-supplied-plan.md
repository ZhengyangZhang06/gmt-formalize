# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1.testform_extension-a1.ambient_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-foundations-a1-acdc5a2d5e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1.testform_extension-a1`
- Child key: `ambient_extension`
- Declaration: `Submission.dimred_mbl_fnd_tfe_ambient_extension`
- Exact Lean type: `∀ (P n d : ℕ) (c : Covector (Euclid P) n ≃L[ℝ] EuclideanSpace ℝ (Fin d)) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (m : Set (Euclid P) → ℝ), IsOpen U → (∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖c α‖) → (∀ (W : Set (Euclid P)) (ω : TestFormOn U n) (r : ℝ), IsOpen W → CompactlyContained W U → tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ r) → |T ω| ≤ r * m W) → ∃ Φ : (Euclid P → Covector (Euclid P) n) → ℝ, (∀ G₁ G₂ : Euclid P → Covector (Euclid P) n, Continuous G₁ → HasCompactSupport G₁ → tsupport G₁ ⊆ U → Continuous G₂ → HasCompactSupport G₂ → tsupport G₂ ⊆ U → Φ (G₁ + G₂) = Φ G₁ + Φ G₂) ∧ (∀ (t : ℝ) (G : Euclid P → Covector (Euclid P) n), Continuous G → HasCompactSupport G → tsupport G ⊆ U → Φ (t • G) = t * Φ G) ∧ (∀ ω : TestFormOn U n, Φ (ω : DifferentialForm (Euclid P) n) = T ω) ∧ ∀ (W : Set (Euclid P)) (G : Euclid P → Covector (Euclid P) n) (r : ℝ), IsOpen W → CompactlyContained W U → Continuous G → HasCompactSupport G → tsupport G ⊆ W → (∀ x, covectorEuclideanNorm (G x) ≤ r) → |Φ G| ≤ r * m W`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1.testform_extension-a1.uniform_approx-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1.testform_extension-a1.limit_functional-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
