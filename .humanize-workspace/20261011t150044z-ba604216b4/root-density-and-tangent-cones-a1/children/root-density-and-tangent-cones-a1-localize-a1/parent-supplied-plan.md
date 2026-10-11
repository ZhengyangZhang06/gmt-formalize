# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.localize-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-localize-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1`
- Child key: `localize`
- Declaration: `Submission.dtc_localize`
- Exact Lean type: `∀ (P n : ℕ) (U A : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → 0 < n → IsMinimizingIn T A → IsOpen (U \ boundarySupport T) ∧ IsMinimizingIn (T.restrictDomain (Set.sdiff_subset : U \ boundarySupport T ⊆ U)) A ∧ BoundaryVanishes (T.restrictDomain (Set.sdiff_subset : U \ boundarySupport T ⊆ U)) ∧ (T.restrictDomain (Set.sdiff_subset : U \ boundarySupport T ⊆ U)).support ⊆ T.support ∧ ∀ W : Set (Euclid P), W ⊆ U \ boundarySupport T → (T.restrictDomain (Set.sdiff_subset : U \ boundarySupport T ⊆ U)).massOn W = T.massOn W`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.vanish_off_support-a1`
- `root.density_and_tangent_cones-a1.mass_eq_measure-a1`
- `root.density_and_tangent_cones-a1.im_sub-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
