# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.lp_monotonicity-a1.abstract_monotonicity-a1.integrating_factor_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-lp-monotonicity-a1-abstract-monotonicity-a1-1b9fb0f412/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.lp_monotonicity-a1.abstract_monotonicity-a1`
- Child key: `integrating_factor_limit`
- Declaration: `Submission.ted_lpm_am_integrating_factor_limit`
- Exact Lean type: `∀ (R β M K Λ : ℝ) (a : ℕ → ℝ → ℝ) (a₀ : ℝ → ℝ) (Q : ℕ → ℝ → ℝ) (Q₀ : ℝ → ℝ), 0 < R → β < 1 → 0 < Λ → K * R ^ (1 - β) / (1 - β) ≤ Λ / 4 → (∀ k, AEStronglyMeasurable (a k) (volume.restrict (Ioc 0 R))) → (∀ k t, 0 < t → t ≤ R → |a k t| ≤ M * t ^ (-β)) → (∀ t, 0 < t → t ≤ R → Tendsto (fun k => a k t) atTop (𝓝 (a₀ t))) → (∀ t, 0 < t → t ≤ R → |a₀ t| ≤ K * t ^ (-β)) → (∀ t, 0 < t → t ≤ R → Tendsto (fun k => Q k t) atTop (𝓝 (Q₀ t))) → (∀ k s r, 0 < s → s ≤ r → r ≤ R → Real.exp (-∫ t in (0)..s, a k t) * Q k s ≤ Real.exp (-∫ t in (0)..r, a k t) * Q k r) → (∀ r, 0 < r → r ≤ R → Real.exp (-Λ) ≤ Real.exp (-∫ t in (0)..r, a₀ t) ∧ Real.exp (-∫ t in (0)..r, a₀ t) ≤ Real.exp Λ ∧ |Real.exp (-∫ t in (0)..r, a₀ t) - 1| ≤ Real.exp (Λ / 2) / 2 * Λ * (r / R) ^ (1 - β) ∧ (Λ ≤ 1 → |Real.exp (-∫ t in (0)..r, a₀ t) - 1| ≤ Λ * (r / R) ^ (1 - β))) ∧ (∀ s r, 0 < s → s ≤ r → r ≤ R → Real.exp (-∫ t in (0)..s, a₀ t) * Q₀ s ≤ Real.exp (-∫ t in (0)..r, a₀ t) * Q₀ r)`

## Sibling prerequisites

- `root.tilt_excess_decay-a1.lp_monotonicity-a1.abstract_monotonicity-a1.exp_perturbation_bounds-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
