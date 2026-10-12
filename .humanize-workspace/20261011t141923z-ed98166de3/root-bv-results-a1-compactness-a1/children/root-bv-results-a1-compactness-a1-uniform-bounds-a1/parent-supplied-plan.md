# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.bv_results-a1.compactness-a1.uniform_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-compactness-a1-uniform-bounds-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.bv_results-a1.compactness-a1`
- Child key: `uniform_bounds`
- Declaration: `Submission.bv_compactness_uniform_bounds`
- Exact Lean type: `∀ (n : ℕ) (W : Set (Rn n)) (u : ℕ → Rn n → ℝ), IsOpen W → volume W < ⊤ → ⨆ k, (∫⁻ x in W, ‖u k x‖ₑ + Chapter02.bvVariationOn (u k) W) < ⊤ → ∃ c : ℝ, 0 ≤ c ∧ ∀ k, (∫⁻ x in W, ‖u k x‖ₑ) ≤ ENNReal.ofReal c ∧ Chapter02.bvVariationOn (u k) W ≤ ENNReal.ofReal c`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
