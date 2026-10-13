# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.im_closure-a1.density_zero_off_set-a1.quotient_rescale-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-im-closure-a1-density-zero-off-set-a1-5ae7522cf5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.im_closure-a1.density_zero_off_set-a1`
- Child key: `quotient_rescale`
- Declaration: `Submission.iwl_imc_quotient_rescale_tendsto_zero`
- Exact Lean type: `∀ (k : ℕ) (F : ℝ → ℝ≥0∞), Tendsto (fun ρ : ℝ => F ρ / ENNReal.ofReal (ρ ^ k)) (𝓝[>] 0) (𝓝 0) → ∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ k)⁻¹) * F (R * r)) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
