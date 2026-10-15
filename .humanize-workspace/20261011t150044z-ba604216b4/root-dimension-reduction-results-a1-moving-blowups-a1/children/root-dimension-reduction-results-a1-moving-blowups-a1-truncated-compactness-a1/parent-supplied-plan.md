# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.truncated_compactness-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-truncated-compactness-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1`
- Child key: `truncated_compactness`
- Declaration: `Submission.dimred_mbl_truncated_compactness`
- Exact Lean type: `∀ (P m : ℕ) (Us : ℕ → Set (Euclid P)) (Ss : (j : ℕ) → GeometricCurrentOn (Us j) (m + 1)), (∀ j, IsOpen (Us j)) → (∀ R : ℝ, ∀ᶠ j in atTop, closedBall (0 : Euclid P) R ⊆ Us j) → (∀ j, IsIntegerMultiplicity (Ss j)) → (∀ R : ℝ, ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ᶠ j in atTop, (Ss j).massOn (ball 0 R) ≤ c) → (∀ j, (Ss j).boundary = 0) → ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (Ŝ : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (ρ : ℕ → ℝ), StrictMono φ ∧ IsIntegerMultiplicity C ∧ C.boundary = 0 ∧ ConvergesWeakly (fun j => Ss (φ j)) C ∧ (∀ j, IsIntegerMultiplicity (Ŝ j)) ∧ (∀ W : Set (Euclid P), IsOpen W → Bornology.IsBounded W → ⨆ j, ((Ŝ j).massOn W + (Ŝ j).boundary.massOn W) < ∞) ∧ WeaklyConvergesOn Ŝ C ∧ Tendsto ρ atTop atTop ∧ (∀ j, closedBall (0 : Euclid P) (ρ j) ⊆ Us (φ j)) ∧ ∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ ball 0 (ρ j) → Ŝ j ω = currentEval (Ss (φ j)) (ω : DifferentialForm (Euclid P) (m + 1))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.slicing-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
