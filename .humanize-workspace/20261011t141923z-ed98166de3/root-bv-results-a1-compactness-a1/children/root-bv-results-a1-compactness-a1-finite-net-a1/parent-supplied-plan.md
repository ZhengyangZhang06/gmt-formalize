# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.bv_results-a1.compactness-a1.finite_net-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-compactness-a1-finite-net-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.bv_results-a1.compactness-a1`
- Child key: `finite_net`
- Declaration: `Submission.bv_lintegral_finite_net_of_lipschitz_approx`
- Exact Lean type: `∀ (n : ℕ) (Q : Set (Rn n)) (u : ℕ → Rn n → ℝ), IsCompact Q → (∀ k, IntegrableOn (u k) Q volume) → (∀ ε : ℝ, 0 < ε → ∃ (B Λ : ℝ) (w : ℕ → Rn n → ℝ), (∀ k, ∀ x ∈ Q, |w k x| ≤ B) ∧ (∀ k, ∀ x ∈ Q, ∀ y ∈ Q, |w k x - w k y| ≤ Λ * ‖x - y‖) ∧ ∀ k, (∫⁻ x in Q, ‖u k x - w k x‖ₑ) ≤ ENNReal.ofReal ε) → ∀ ε : ℝ, 0 < ε → ∃ F : Finset ℕ, ∀ k, ∃ j ∈ F, (∫⁻ x in Q, ‖u k x - u j x‖ₑ) < ENNReal.ofReal ε`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
