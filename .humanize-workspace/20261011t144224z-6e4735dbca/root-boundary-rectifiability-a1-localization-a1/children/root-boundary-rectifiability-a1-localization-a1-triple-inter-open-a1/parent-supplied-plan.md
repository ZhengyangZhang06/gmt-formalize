# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.boundary_rectifiability-a1.localization-a1.triple_inter_open-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-localization-a1-triple-inter-open-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.boundary_rectifiability-a1.localization-a1`
- Child key: `triple_inter_open`
- Declaration: `Submission.br_loc_triple_inter_open`
- Exact Lean type: `∀ (P n : ℕ) (U U' V M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → IsOpen V → M ∩ V ⊆ U' → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U' → IntegrableOn θ (M ∩ V ∩ K) (μHE[n] : Measure (Eucl P))) → IsRectifiableTriple U' n (M ∩ V) θ ξ`

## Sibling prerequisites

- `root.boundary_rectifiability-a1.tangent_locality-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
