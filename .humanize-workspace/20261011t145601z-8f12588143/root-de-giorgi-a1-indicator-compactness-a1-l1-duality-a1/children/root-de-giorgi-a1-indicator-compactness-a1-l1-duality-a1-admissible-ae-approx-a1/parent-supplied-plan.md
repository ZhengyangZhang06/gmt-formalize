# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.indicator_compactness-a1.l1_duality-a1.admissible_ae_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-l1-duality-a1-admissible-ae-approx-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.indicator_compactness-a1.l1_duality-a1`
- Child key: `admissible_ae_approx`
- Declaration: `Submission.indCompact_l1Dual_exists_admissible_ae_tendsto`
- Exact Lean type: `∀ (N : ℕ) (R : ℝ) (s : Rn N → ℝ), 0 < R → AEStronglyMeasurable s volume → (∀ y, |s y| ≤ 1) → (∀ y, y ∉ Metric.ball (0 : Rn N) R → s y = 0) → ∃ ψ : ℕ → Rn N → ℝ, (∀ j, ContDiff ℝ 1 (ψ j)) ∧ (∀ j, HasCompactSupport (ψ j)) ∧ (∀ j, tsupport (ψ j) ⊆ Metric.ball (0 : Rn N) R) ∧ (∀ j y, |ψ j y| ≤ 1) ∧ ∀ᵐ y ∂(volume : Measure (Rn N)), Tendsto (fun j ↦ ψ j y) atTop (𝓝 (s y))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
