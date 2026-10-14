# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.minimizing_and_measures-a1.minimality-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-minimizing-and-07926d6d5f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.minimizing_and_measures-a1`
- Child key: `minimality`
- Declaration: `Submission.dimred_mbl_mm_isMinimizingIn_univ`
- Exact Lean type: `∀ (P n : ℕ) (Us : ℕ → Set (Euclid P)) (Ss : (j : ℕ) → GeometricCurrentOn (Us j) n) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), (∀ R : ℝ, ∀ᶠ j in atTop, closedBall (0 : Euclid P) R ⊆ Us j) → IsIntegerMultiplicity C → ConvergesWeakly Ss C → (∀ (K : Set (Euclid P)) (ε : ℝ), IsCompact K → 0 < ε → ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ W : Set (Euclid P), IsOpen W ∧ K ⊆ W ∧ W ⊆ thickening ε K ∧ ∃ φ' : ℕ → ℕ, StrictMono φ' ∧ ∀ S : GeometricCurrentOn (univ : Set (Euclid P)) n, IsIntegerMultiplicity S → SameBoundary S C → (S - C).support ⊆ K → limsup (fun j => (Ss (ψ (φ' j))).massOn W) atTop ≤ S.massOn W) → IsMinimizingIn C univ`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.moving_blowups-a1.minimizing_and_measures-a1.mass_lsc-a1`
- `root.compactness_of_minimizing_currents-a1.minimality_localizes-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
