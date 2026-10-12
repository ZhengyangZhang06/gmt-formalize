# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.polyhedral_approximation-a1.restriction_tau-a1.tau_integrability-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-restriction-tau-a1-tau-integrability-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.polyhedral_approximation-a1.restriction_tau-a1`
- Child key: `tau_integrability`
- Declaration: `Submission.polyhedral_approx_rt_tau_integrableOn`
- Exact Lean type: `∀ (P n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∀ c : Covector (Eucl P) n, IntegrableOn (fun x => θ x * ξ x c) K ((μHE[n] : Measure (Eucl P)).restrict M)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
