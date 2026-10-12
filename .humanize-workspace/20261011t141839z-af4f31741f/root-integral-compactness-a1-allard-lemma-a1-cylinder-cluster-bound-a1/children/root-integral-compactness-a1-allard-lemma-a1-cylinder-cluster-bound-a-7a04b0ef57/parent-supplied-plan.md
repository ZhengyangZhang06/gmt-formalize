# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1.cylinder_grouping-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-cylinder-cluster-bound-a-7a04b0ef57/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1`
- Child key: `cylinder_grouping`
- Declaration: `Submission.intcpt_allard_ccb_cylinder_grouping`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) (P : Grassmannian N n) (x : Euclidean N) (s Z : Finset (Euclidean N)) (d ρ S u : ℝ), (∀ y ∈ s, Grassmannian.project P y = x) → Z ⊆ s → 0 < d → (∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → d ≤ ‖y - y'‖) → 0 < ρ → 0 ≤ S → S ≤ u * ρ → u ≤ 1 → (∀ y ∈ s, ∃ z ∈ Z, ‖y - z‖ ≤ S) → ∑ y ∈ s, μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2}) / ENNReal.ofReal ρ ^ n ≤ ENNReal.ofReal (1 + (2 ^ n - 1) * u) * ∑ y ∈ Z, μ (closedBall y (ρ + S) ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < d / 2 + S}) / ENNReal.ofReal (ρ + S) ^ n`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
