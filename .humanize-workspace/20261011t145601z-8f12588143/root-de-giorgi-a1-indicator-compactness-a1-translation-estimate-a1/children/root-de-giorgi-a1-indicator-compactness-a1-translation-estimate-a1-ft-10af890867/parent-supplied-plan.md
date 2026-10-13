# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.indicator_compactness-a1.translation_estimate-a1.ftc_fubini_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-translation-estimate-a1-ft-10af890867/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.indicator_compactness-a1.translation_estimate-a1`
- Child key: `ftc_fubini_identity`
- Declaration: `Submission.indCompact_transEst_setIntegral_shift_sub_ftc`
- Exact Lean type: `∀ (N : ℕ) (F : Set (Rn N)) (ψ : Rn N → ℝ) (h : Rn N), ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∫ z in F, (ψ (z - h) - ψ z) = -∫ t in (0 : ℝ)..1, ∫ z in F, fderiv ℝ ψ (z - t • h) h`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
