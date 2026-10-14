# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.polyhedral_approximation-a1.finite_mass_approximation-a1.flat_convergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-finite-mass-approximation-a1-flat-co-0f93f60fe5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.polyhedral_approximation-a1.finite_mass_approximation-a1`
- Child key: `flat_convergence`
- Declaration: `Submission.polyhedral_approx_flat_seq_tendsto`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Eucl P)) (X Pc S : ℕ → GeometricCurrentOn U n) (R : ℕ → GeometricCurrentOn U (n + 1)), (∀ (k : ℕ) (ω : TestFormOn U n), X k ω - Pc k ω = (R k).boundary ω + S k ω) → Tendsto (fun k => (R k).mass) atTop (𝓝 0) → Tendsto (fun k => (S k).mass) atTop (𝓝 0) → ∀ ω : TestFormOn U n, Tendsto (fun k => Pc k ω - X k ω) atTop (𝓝 0)`

## Sibling prerequisites

- `root.boundary_rectifiability-a1.lattice_approximation-a1.mass_estimate-a1`
- `root.polyhedral_approximation-a1.finite_mass_approximation-a1.testform_bounded-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
