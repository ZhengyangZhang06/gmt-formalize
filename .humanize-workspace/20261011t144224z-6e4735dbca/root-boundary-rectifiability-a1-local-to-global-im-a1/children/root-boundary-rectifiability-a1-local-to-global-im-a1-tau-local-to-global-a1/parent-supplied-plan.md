# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.boundary_rectifiability-a1.local_to_global_im-a1.tau_local_to_global-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-local-to-global-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.boundary_rectifiability-a1.local_to_global_im-a1`
- Child key: `tau_local_to_global`
- Declaration: `Submission.ltg_tau_local_to_global`
- Exact Lean type: `∀ (P k : ℕ) (U : Set (Eucl P)) (X : GeometricCurrentOn U k) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k), IsRectifiableTriple U k M θ ξ → (∀ x ∈ U, ∃ V : Set (Eucl P), IsOpen V ∧ x ∈ V ∧ ∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ V → X ω = tauAction k M θ ξ ω) → ∀ ω : TestFormOn U k, X ω = tauAction k M θ ξ ω`

## Sibling prerequisites

- `root.boundary_rectifiability-a1.local_to_global_im-a1.tau_integrable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
