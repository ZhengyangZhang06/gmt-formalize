# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.stationary_cone_flat-a1.constancy_plane-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-stationary-cone-flat-a1-constancy-plane-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1.stationary_cone_flat-a1`
- Child key: `constancy_plane`
- Declaration: `Submission.allard_tc_scf_constancy_plane`
- Exact Lean type: `ConstancyTheorem → ∀ (N n : ℕ) (C : Varifold N n (univ : Set (Euclidean N))) (T : Grassmannian N n), C.Stationary → C.weight.support ⊆ (T.plane : Set (Euclidean N)) → ∃ θ : ℝ, 0 ≤ θ ∧ C.measure = ENNReal.ofReal θ • planeVarifoldMeasure T`

## Sibling prerequisites

- `root.allard_tangent_cones-a1.stationary_cone_flat-a1.subspace_submanifold-a1`
- `root.allard_tangent_cones-a1.stationary_cone_flat-a1.subspace_tangent-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
