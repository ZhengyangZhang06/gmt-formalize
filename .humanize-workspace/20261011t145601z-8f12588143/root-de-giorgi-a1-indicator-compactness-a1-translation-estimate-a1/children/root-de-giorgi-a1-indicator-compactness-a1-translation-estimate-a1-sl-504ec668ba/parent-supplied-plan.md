# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.indicator_compactness-a1.translation_estimate-a1.slice_divergence_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-translation-estimate-a1-sl-504ec668ba/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.indicator_compactness-a1.translation_estimate-a1`
- Child key: `slice_divergence_bound`
- Declaration: `Submission.indCompact_transEst_abs_setIntegral_fderiv_le`
- Exact Lean type: `∀ (N : ℕ) (F : Set (Rn N)) (R C : ℝ), (∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ Metric.ball (0 : Rn N) (R + 1) → (∀ y, ‖g y‖ ≤ 1) → ∫ y in F, Poincare.SimonGMT.Chapter02.euclideanDivergence g y ≤ C) → ∀ ψ : Rn N → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball (0 : Rn N) R → (∀ y, |ψ y| ≤ 1) → ∀ a h : Rn N, ‖a‖ ≤ 1 → |∫ z in F, fderiv ℝ ψ (z - a) h| ≤ C * ‖h‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
