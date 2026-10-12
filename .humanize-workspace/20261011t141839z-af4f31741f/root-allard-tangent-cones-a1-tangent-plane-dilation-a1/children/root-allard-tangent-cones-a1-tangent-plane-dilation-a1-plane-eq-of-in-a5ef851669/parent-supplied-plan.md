# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.tangent_plane_dilation-a1.plane_eq_of_integral_eq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-tangent-plane-dilation-a1-plane-eq-of-in-a5ef851669/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1.tangent_plane_dilation-a1`
- Child key: `plane_eq_of_integral_eq`
- Declaration: `Submission.allard_tc_tpd_plane_eq_of_integral_eq`
- Exact Lean type: `∀ (N n : ℕ) (T T' : Grassmannian N n), (∀ g : C_c(Euclidean N, ℝ), ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n] = ∫ y in (T'.plane : Set (Euclidean N)), g y ∂μHE[n]) → T' = T`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
