# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.slice_limit-a1.local_closure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-788730048c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.slice_limit-a1`
- Child key: `local_closure`
- Declaration: `Submission.dmcbr_sl_isIntegerMultiplicity_of_liminf_bounded`
- Exact Lean type: `∀ d : ℕ, (∀ (P : ℕ) (U : Set (Euclid P)) (Ts : ℕ → GeometricCurrentOn U d) (T : GeometricCurrentOn U d), IsOpen U → (∀ j, IsIntegerMultiplicity (Ts j)) → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) < ∞) → WeaklyConvergesOn Ts T → IsIntegerMultiplicity T) → (∀ (P : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U d), IsOpen U → ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → X.massOn W < ∞) → (∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ ∃ h : ball x r ⊆ U, IsIntegerMultiplicity (X.restrictDomain h)) → IsIntegerMultiplicity X) ∧ (∀ (V : Set (Euclid P)) (h : V ⊆ U), IsOpen V → IsIntegerMultiplicity X → IsIntegerMultiplicity (X.restrictDomain h))) → ∀ (P : ℕ) (Zs : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) d) (Z : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ i, IsIntegerMultiplicity (Zs i)) → WeaklyConvergesOn Zs Z → (∀ k : ℕ, liminf (fun i => (Zs i).massOn (ball (0 : Euclid P) k) + boundaryMassOn (Zs i) (ball (0 : Euclid P) k)) atTop < ∞) → IsIntegerMultiplicity Z`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
