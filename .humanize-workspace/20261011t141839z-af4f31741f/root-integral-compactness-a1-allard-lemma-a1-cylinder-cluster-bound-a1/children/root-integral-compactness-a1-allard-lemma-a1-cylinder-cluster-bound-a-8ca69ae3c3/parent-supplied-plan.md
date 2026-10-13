# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1.reduction_step-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-cylinder-cluster-bound-a-8ca69ae3c3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1`
- Child key: `reduction_step`
- Declaration: `Submission.intcpt_allard_ccb_reduction_step`
- Exact Lean type: `∀ (N n : ℕ) (K : ℝ) (m : ℕ), (∀ (t : Finset (Euclidean N)) (d : ℝ), 2 ≤ t.card → 0 < d → (∀ y ∈ t, ∀ y' ∈ t, y ≠ y' → d ≤ ‖y - y'‖) → (∃ y ∈ t, ∃ y' ∈ t, y ≠ y' ∧ ‖y - y'‖ ≤ d) → ∃ (Z : Finset (Euclidean N)) (S : ℝ), Z ⊆ t ∧ Z.card < t.card ∧ 0 ≤ S ∧ S ≤ (10 * (t.card : ℝ)) ^ t.card * d ∧ (∀ y ∈ t, ∃ z ∈ Z, ‖y - z‖ ≤ S) ∧ ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → 2 * d + 4 * S ≤ ‖z - z'‖) → 0 ≤ K → ∀ δ ε : ℝ, 0 < δ → δ ≤ 1 / (4 * (10 * ((m : ℝ) + 1)) ^ (m + 1)) → 0 < ε → ε ≤ δ ^ 4 → ∀ (μ : Measure (Euclidean N)) (P : Grassmannian N n) (x : Euclidean N) (s : Finset (Euclidean N)), 2 ≤ s.card → s.card ≤ m + 1 → (∀ y ∈ s, Grassmannian.project P y = x ∧ ‖y - Grassmannian.project P y‖ < ε ∧ ∀ τ σ ρ : ℝ, 0 < τ → τ ≤ 1 → 0 < σ → σ ≤ ρ → ρ < 1 → μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) / ENNReal.ofReal ρ ^ n + ENNReal.ofReal (K * ε * ρ / τ)) → ∀ σ τ : ℝ, 0 < σ → σ ≤ δ ^ 2 → 2 * δ ^ 2 * σ ≤ τ → (∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → 4 * τ ≤ ‖y - y'‖) → ∃ (Z : Finset (Euclidean N)) (σ' τ' : ℝ), Z ⊆ s ∧ Z.card ≤ m ∧ 0 < σ' ∧ σ' ≤ δ ^ 2 ∧ 2 * δ ^ 2 * σ' ≤ τ' ∧ (∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → 4 * τ' ≤ ‖z - z'‖) ∧ ∑ y ∈ s, μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ ENNReal.ofReal (1 + (2 ^ n - 1) * (4 * (10 * ((m : ℝ) + 1)) ^ (m + 1)) * δ ^ 2) * ∑ y ∈ Z, μ (closedBall y σ' ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ'}) / ENNReal.ofReal σ' ^ n + ENNReal.ofReal (((m : ℝ) + 1) * K * δ ^ 2)`

## Sibling prerequisites

- `root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1.cylinder_grouping-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
