# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.flat_cauchy_limit-a1.telescope_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-flat-cauchy-limit-a1-telescope-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.flat_cauchy_limit-a1`
- Child key: `telescope_limit`
- Declaration: `Submission.fiw_fcl_telescope_limit`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Eucl P)) (Tr : ℕ → GeometricCurrentOn U n) (T : GeometricCurrentOn U n) (R : ℕ → GeometricCurrentOn U (n + 1)) (S : ℕ → GeometricCurrentOn U n) (X : GeometricCurrentOn U (n + 1)) (Y : GeometricCurrentOn U n) (ℓ : ℕ), (∀ r ω, Tr r ω - Tr (r + 1) ω = (R r).boundary ω + S r ω) → WeaklyConvergesOn Tr T → (∀ η, HasSum (fun k => R (ℓ + k) η) (X η)) → (∀ ω, HasSum (fun k => S (ℓ + k) ω) (Y ω)) → ∀ ω, Tr ℓ ω - T ω = X.boundary ω + Y ω`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
