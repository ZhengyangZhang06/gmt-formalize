# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.cluster_selection-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-cluster-selection-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1`
- Child key: `cluster_selection`
- Declaration: `Submission.intcpt_allard_cluster_selection`
- Exact Lean type: `∀ (N : ℕ) (s : Finset (Euclidean N)) (d : ℝ), 2 ≤ s.card → 0 < d → (∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → d ≤ ‖y - y'‖) → (∃ y ∈ s, ∃ y' ∈ s, y ≠ y' ∧ ‖y - y'‖ ≤ d) → ∃ (Z : Finset (Euclidean N)) (S : ℝ), Z ⊆ s ∧ Z.card < s.card ∧ 0 ≤ S ∧ S ≤ (10 * (s.card : ℝ)) ^ s.card * d ∧ (∀ y ∈ s, ∃ z ∈ Z, ‖y - z‖ ≤ S) ∧ ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → 2 * d + 4 * S ≤ ‖z - z'‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
