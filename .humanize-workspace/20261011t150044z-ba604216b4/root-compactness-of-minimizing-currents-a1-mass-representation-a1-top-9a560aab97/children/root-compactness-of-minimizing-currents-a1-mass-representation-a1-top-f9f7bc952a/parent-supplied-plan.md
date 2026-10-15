# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.top_dim_null-a1.null_set_cutoffs-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-top-f9f7bc952a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.top_dim_null-a1`
- Child key: `null_set_cutoffs`
- Declaration: `Submission.cmr_tdn_null_set_cutoffs`
- Exact Lean type: `∀ (n : ℕ) (K : Set (Euclid n)), IsCompact K → volume K = 0 → ∃ a : ℕ → Euclid n → ℝ, (∀ k, ContDiff ℝ (⊤ : ℕ∞) (a k)) ∧ (∀ k, HasCompactSupport (a k)) ∧ (∀ k y, 0 ≤ a k y) ∧ (∀ k y, a k y ≤ 1) ∧ (∀ k, ∀ y ∈ K, a k y = 1) ∧ (∀ y, y ∉ K → ∀ᶠ k in atTop, a k y = 0) ∧ Tendsto (fun k => ∫ y, a k y) atTop (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
