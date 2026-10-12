# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_semicontinuity-a1.lower_density_ae-a1.relcompact_exhaustion_ae-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-density-semicontinuity-a1-lower-density-ae-a1-relcompact-exhaustion-ae-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_semicontinuity-a1.lower_density_ae-a1`
- Child key: `relcompact_exhaustion_ae`
- Declaration: `Submission.ae_of_forall_relCompactOpen_null_exceptional`
- Exact Lean type: `∀ (N : ℕ) (U : Set (Euclidean N)) (μ : Measure (Euclidean N)) (P : Euclidean N → Prop), IsOpen U → μ Uᶜ = 0 → (∀ W : Set (Euclidean N), IsRelCompactOpenIn W U → ∃ E : Set (Euclidean N), μ E = 0 ∧ ∀ x ∈ W, x ∉ E → P x) → ∀ᵐ x ∂μ, P x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
