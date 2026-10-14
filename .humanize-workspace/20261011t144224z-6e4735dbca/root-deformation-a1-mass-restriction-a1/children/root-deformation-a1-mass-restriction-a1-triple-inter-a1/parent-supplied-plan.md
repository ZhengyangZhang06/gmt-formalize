# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.mass_restriction-a1.triple_inter-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-mass-restriction-a1-triple-inter-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.mass_restriction-a1`
- Child key: `triple_inter`
- Declaration: `Submission.dmr_rectifiableTriple_inter`
- Exact Lean type: `∀ (N k : ℕ) (M : Set (Eucl N)) (θ : Eucl N → ℝ) (ξ : Eucl N → NVector (Eucl N) k) (A : Set (Eucl N)), IsRectifiableTriple (univ : Set (Eucl N)) k M θ ξ → MeasurableSet A → IsRectifiableTriple (univ : Set (Eucl N)) k (M ∩ A) θ ξ`

## Sibling prerequisites

- `root.deformation-a1.mass_restriction-a1.tangent_inter-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
