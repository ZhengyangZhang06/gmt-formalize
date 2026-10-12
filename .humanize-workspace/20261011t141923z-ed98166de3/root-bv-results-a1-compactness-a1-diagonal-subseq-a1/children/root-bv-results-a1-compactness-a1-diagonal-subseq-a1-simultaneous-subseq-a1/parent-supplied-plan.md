# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.bv_results-a1.compactness-a1.diagonal_subseq-a1.simultaneous_subseq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-compactness-a1-diagonal-subseq-a1-simultaneous-subseq-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.bv_results-a1.compactness-a1.diagonal_subseq-a1`
- Child key: `simultaneous_subseq`
- Declaration: `Submission.bv_exists_subseq_tendsto_lintegral_of_finite_nets`
- Exact Lean type: `∀ (n : ℕ) (Q : ℕ → Set (Rn n)) (u : ℕ → Rn n → ℝ), (∀ j k, IntegrableOn (u k) (Q j) volume) → (∀ j, ∀ ε : ℝ, 0 < ε → ∃ F : Finset ℕ, ∀ k, ∃ i ∈ F, (∫⁻ x in Q j, ‖u k x - u i x‖ₑ) < ENNReal.ofReal ε) → ∃ (ψ : ℕ → ℕ) (G : ℕ → Rn n → ℝ), StrictMono ψ ∧ (∀ j, IntegrableOn (G j) (Q j) volume) ∧ ∀ j, Tendsto (fun k ↦ ∫⁻ x in Q j, ‖u (ψ k) x - G j x‖ₑ) atTop (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
