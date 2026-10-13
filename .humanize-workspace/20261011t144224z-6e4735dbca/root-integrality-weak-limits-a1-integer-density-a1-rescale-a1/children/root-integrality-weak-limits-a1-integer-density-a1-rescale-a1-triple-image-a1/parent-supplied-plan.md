# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.rescale-a1.triple_image-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-rescale-a1-triple-image-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.rescale-a1`
- Child key: `triple_image`
- Declaration: `Submission.ind_rs_rectifiableTriple_dilation`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (x : Eucl P) (r : ℝ), 0 < r → IsRectifiableTriple (univ : Set (Eucl P)) n M θ ξ → IsRectifiableTriple (univ : Set (Eucl P)) n ((fun y => r⁻¹ • (y - x)) '' M) (fun z => θ (x + r • z)) (fun z => ξ (x + r • z))`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.integer_density-a1.rescale-a1.dilation_measure-a1`
- `root.integrality_weak_limits-a1.integer_density-a1.rescale-a1.weighted_tangent-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
