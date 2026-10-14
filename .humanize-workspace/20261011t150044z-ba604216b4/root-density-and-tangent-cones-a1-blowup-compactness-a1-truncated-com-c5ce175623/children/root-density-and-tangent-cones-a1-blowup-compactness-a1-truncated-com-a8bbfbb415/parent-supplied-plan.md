# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.slice_limit-a1.local_closure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-a8bbfbb415/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.slice_limit-a1`
- Child key: `local_closure`
- Declaration: `Submission.dtc_bc_tc_cl_sl_isIntegerMultiplicity_of_liminf_bounds`
- Exact Lean type: `∀ (P d : ℕ), (∀ (U : Set (Euclid P)) (Ts : ℕ → GeometricCurrentOn U d) (T : GeometricCurrentOn U d), IsOpen U → (∀ j, IsIntegerMultiplicity (Ts j)) → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) < ∞) → WeaklyConvergesOn Ts T → IsIntegerMultiplicity T) → (∀ (U : Set (Euclid P)) (X : GeometricCurrentOn U d), IsOpen U → ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → X.massOn W < ∞) → (∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ ∃ h : ball x r ⊆ U, IsIntegerMultiplicity (X.restrictDomain h)) → IsIntegerMultiplicity X) ∧ (∀ (V : Set (Euclid P)) (h : V ⊆ U), IsOpen V → IsIntegerMultiplicity X → IsIntegerMultiplicity (X.restrictDomain h))) → ∀ (Zs : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) d) (Z : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ i, IsIntegerMultiplicity (Zs i)) → WeaklyConvergesOn Zs Z → (∀ k : ℕ, liminf (fun i => (Zs i).massOn (ball (0 : Euclid P) ((k : ℝ) + 1)) + boundaryMassOn (Zs i) (ball (0 : Euclid P) ((k : ℝ) + 1))) atTop < ∞) → IsIntegerMultiplicity Z`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
