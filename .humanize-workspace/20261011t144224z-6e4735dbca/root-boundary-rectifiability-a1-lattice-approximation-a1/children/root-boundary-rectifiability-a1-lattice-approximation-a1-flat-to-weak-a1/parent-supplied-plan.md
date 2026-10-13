# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.boundary_rectifiability-a1.lattice_approximation-a1.flat_to_weak-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-lattice-approximation-a1-flat-to-weak-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.boundary_rectifiability-a1.lattice_approximation-a1`
- Child key: `flat_to_weak`
- Declaration: `Submission.br_la_weaklyConvergesOn_of_flat_decomposition`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Eucl P)) (X : GeometricCurrentOn U (m + 1)) (Pk S : ℕ → GeometricCurrentOn U (m + 1)) (R : ℕ → GeometricCurrentOn U (m + 2)), (∀ (k : ℕ) (ω : TestFormOn U (m + 1)), X ω - Pk k ω = (R k).boundary ω + S k ω) → Tendsto (fun k => (R k).mass) atTop (𝓝 0) → Tendsto (fun k => (S k).mass) atTop (𝓝 0) → WeaklyConvergesOn Pk X`

## Sibling prerequisites

- `root.boundary_rectifiability-a1.lattice_approximation-a1.mass_estimate-a1`
- `root.boundary_rectifiability-a1.lattice_approximation-a1.testform_bounded-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
