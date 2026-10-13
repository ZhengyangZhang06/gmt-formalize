# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-comparison-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1`
- Child key: `local_comparison`
- Declaration: `Submission.dtc_bc_local_comparison`
- Exact Lean type: `∀ (P m : ℕ) (Us As : ℕ → Set (Euclid P)) (Ss : (j : ℕ) → GeometricCurrentOn (Us j) (m + 1)) (Ŝ : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (C : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (ρ : ℕ → ℝ), m + 1 < P → (∀ j, IsOpen (Us j)) → (∀ j, IsMinimizingIn (Ss j) (As j)) → (∀ j, (Ss j).support ⊆ As j) → (∀ R : ℝ, ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ᶠ j in atTop, (Ss j).massOn (ball 0 R) ≤ c) → (∀ G : ℝ, 0 < G → ∃ πs : ℕ → Euclid P → Euclid P, (∀ᶠ j in atTop, ContDiffOn ℝ 1 (πs j) (ball 0 G) ∧ MapsTo (πs j) (ball 0 G) (As j) ∧ (∀ y ∈ As j ∩ ball 0 G, πs j y = y) ∧ ∀ y ∈ ball 0 G, ‖πs j y‖ ≤ 2 * ‖y‖) ∧ ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ y ∈ ball 0 G, ∀ z ∈ ball 0 G, ‖πs j y - πs j z‖ ≤ (1 + η) * ‖y - z‖) → IsIntegerMultiplicity C → (∀ j, IsIntegerMultiplicity (Ŝ j)) → (∀ W : Set (Euclid P), IsOpen W → Bornology.IsBounded W → ⨆ j, ((Ŝ j).massOn W + (Ŝ j).boundary.massOn W) < ∞) → WeaklyConvergesOn Ŝ C → Tendsto ρ atTop atTop → (∀ j, closedBall (0 : Euclid P) (ρ j) ⊆ Us j) → (∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ ball 0 (ρ j) → Ŝ j ω = currentEval (Ss j) (ω : DifferentialForm (Euclid P) (m + 1))) → ∀ (K : Set (Euclid P)) (ε : ℝ), IsCompact K → 0 < ε → ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ W : Set (Euclid P), IsOpen W ∧ K ⊆ W ∧ W ⊆ thickening ε K ∧ ∃ φ' : ℕ → ℕ, StrictMono φ' ∧ ∀ S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity S → SameBoundary S C → (S - C).support ⊆ K → limsup (fun j => (Ss (ψ (φ' j))).massOn W) atTop ≤ S.massOn W`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.measure_locality-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
