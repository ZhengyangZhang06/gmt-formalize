# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.indicator_compactness-a1.mollified_cauchy-a1.mollified_continuous-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-mollified-cauchy-a1-mollif-1ed6c47076/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.indicator_compactness-a1.mollified_cauchy-a1`
- Child key: `mollified_continuous`
- Declaration: `Submission.indCompact_mollCauchy_setIntegral_continuous`
- Exact Lean type: `∀ (N : ℕ) (F : Set (Rn N)) (ρ : Rn N → ℝ), Continuous ρ → HasCompactSupport ρ → Continuous (fun y : Rn N ↦ ∫ z in F, ρ (y - z))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
