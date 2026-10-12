# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.c1_approximation-a1.egorov_sigma_finite-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-c1-approximation-a1-egorov-sigma-finite-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.c1_approximation-a1`
- Child key: `egorov_sigma_finite`
- Declaration: `Submission.egorov_closed_subset_uniformOn_compact_volume`
- Exact Lean type: `∀ (n : ℕ) (η : ℕ → Rn n → ℝ) (g : Rn n → ℝ) (S : Set (Rn n)), (∀ k, Measurable (η k)) → Measurable g → MeasurableSet S → (∀ x ∈ S, Tendsto (fun k => η k x) atTop (𝓝 (g x))) → ∀ ε : ℝ≥0∞, 0 < ε → ∃ A ⊆ S, IsClosed A ∧ volume (S \ A) < ε ∧ ∀ Q : Set (Rn n), IsCompact Q → Q ⊆ A → TendstoUniformlyOn η g atTop Q`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
