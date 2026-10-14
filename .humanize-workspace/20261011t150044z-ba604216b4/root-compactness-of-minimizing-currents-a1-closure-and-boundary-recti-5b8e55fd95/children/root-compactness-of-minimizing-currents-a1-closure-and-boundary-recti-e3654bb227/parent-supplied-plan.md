# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.local_filling-a1.constants-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-e3654bb227/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.local_filling-a1`
- Child key: `constants`
- Declaration: `Submission.cbrldlf_exists_filling_constant`
- Exact Lean type: `∀ (m : ℕ) (c : ℝ), 1 ≤ c → ∃ a : ℝ, 0 < a ∧ ∀ (s F M : ℝ), 0 ≤ s → 0 ≤ F → F ≤ (a * s) ^ (m + 1 + 1) → 0 ≤ M → M ≤ 2 * ((m + 1 + 1 : ℕ) : ℝ) * a * F ^ ((((m + 1 + 1 : ℕ) : ℝ) - 1) / ((m + 1 + 1 : ℕ) : ℝ)) → c * (2 * c * M) ^ ((1 : ℝ) / (m + 1)) * M ≤ F / 2 ∧ (2 * c * M) ^ ((1 : ℝ) / (m + 1)) ≤ s`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
