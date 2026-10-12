# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.divergence_identity-a1.integrability-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-divergence-identity-a1-integrability-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1.divergence_identity-a1`
- Child key: `integrability`
- Declaration: `Submission.tangentialDivergence_meanCurvature_integrableOn`
- Exact Lean type: `∀ (n N : ℕ) (M F : Set (Rn N)) (Y : Rn N → Rn N), MeasurableSet M → ContinuousOn (tangentProjection M) M → ContinuousOn (meanCurvature M) M → (∀ C ⊆ M, IsCompact C → μHE[n] C < ⊤) → ContDiff ℝ 1 Y → IsClosed F → (∀ x ∉ F, Y x = 0) → IsCompact (M ∩ F) → IntegrableOn (tangentialDivergence M Y) M μHE[n] ∧ IntegrableOn (fun y ↦ inner ℝ (Y y) (meanCurvature M y)) M μHE[n]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
