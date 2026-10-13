# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-compactness-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1`
- Child key: `truncated_compactness`
- Declaration: `Submission.dtc_bc_truncated_compactness`
- Exact Lean type: `∀ (P m : ℕ) (Us : ℕ → Set (Euclid P)) (Ss : (j : ℕ) → GeometricCurrentOn (Us j) (m + 1)), m + 1 < P → (∀ j, IsOpen (Us j)) → (∀ R : ℝ, ∀ᶠ j in atTop, closedBall (0 : Euclid P) R ⊆ Us j) → (∀ j, IsIntegerMultiplicity (Ss j)) → (∀ R : ℝ, ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ᶠ j in atTop, (Ss j).massOn (ball 0 R) ≤ c) → (∀ R : ℝ, ∀ᶠ j in atTop, ∀ ω : TestFormOn (Us j) m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ ball 0 R → (Ss j).boundary ω = 0) → ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (Ŝ : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (ρ : ℕ → ℝ), StrictMono φ ∧ IsIntegerMultiplicity C ∧ C.boundary = 0 ∧ ConvergesWeakly (fun j => Ss (φ j)) C ∧ (∀ j, IsIntegerMultiplicity (Ŝ j)) ∧ (∀ W : Set (Euclid P), IsOpen W → Bornology.IsBounded W → ⨆ j, ((Ŝ j).massOn W + (Ŝ j).boundary.massOn W) < ∞) ∧ WeaklyConvergesOn Ŝ C ∧ Tendsto ρ atTop atTop ∧ (∀ j, closedBall (0 : Euclid P) (ρ j) ⊆ Us (φ j)) ∧ ∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ ball 0 (ρ j) → Ŝ j ω = currentEval (Ss (φ j)) (ω : DifferentialForm (Euclid P) (m + 1))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
