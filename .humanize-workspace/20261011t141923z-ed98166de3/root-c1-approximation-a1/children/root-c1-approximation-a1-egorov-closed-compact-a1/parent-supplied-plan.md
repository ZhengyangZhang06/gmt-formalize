# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.c1_approximation-a1.egorov_closed_compact-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-c1-approximation-a1-egorov-closed-compact-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.c1_approximation-a1`
- Child key: `egorov_closed_compact`
- Declaration: `Submission.c1approx_egorov_closed_compact_uniform`
- Exact Lean type: `∀ (n : ℕ) (C : Set (Rn n)) (F : ℕ → Rn n → ℝ) (G : Rn n → ℝ), MeasurableSet C → (∀ k, Measurable (F k)) → Measurable G → (∀ x ∈ C, Tendsto (fun k ↦ F k x) atTop (𝓝 (G x))) → ∀ ε : ℝ, 0 < ε → ∃ A ⊆ C, IsClosed A ∧ volume (C \ A) < ENNReal.ofReal ε ∧ ∀ K ⊆ A, IsCompact K → TendstoUniformlyOn F G atTop K`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
