# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-cylinder-cluster-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1`
- Child key: `cylinder_cluster_bound`
- Declaration: `Submission.intcpt_allard_cylinder_cluster_bound`
- Exact Lean type: `∀ (N n : ℕ) (K : ℝ) (m : ℕ), 0 ≤ K → ∃ c δm : ℝ, 0 ≤ c ∧ 0 < δm ∧ ∀ δ ε : ℝ, 0 < δ → δ ≤ δm → 0 < ε → ε ≤ δ ^ 4 → ∀ (μ : Measure (Euclidean N)) (P : Grassmannian N n) (x : Euclidean N) (s : Finset (Euclidean N)), s.card ≤ m → (∀ y ∈ s, Grassmannian.project P y = x ∧ ‖y - Grassmannian.project P y‖ < ε ∧ MonotoneOn (fun r : ℝ ↦ ENNReal.ofReal (Real.exp (ε * r)) * μ (closedBall y r) / ENNReal.ofReal r ^ n) (Ioo 0 1) ∧ ∀ τ σ ρ : ℝ, 0 < τ → τ ≤ 1 → 0 < σ → σ ≤ ρ → ρ < 1 → μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) / ENNReal.ofReal ρ ^ n + ENNReal.ofReal (K * ε * ρ / τ)) → ∀ σ τ : ℝ, 0 < σ → σ ≤ δ ^ 2 → 2 * δ ^ 2 * σ ≤ τ → (∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → 4 * τ ≤ ‖y - y'‖) → ∑ y ∈ s, μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ ENNReal.ofReal (1 + c * δ ^ 2) * μ (closedBall x 1) + ENNReal.ofReal (c * δ ^ 2)`

## Sibling prerequisites

- `root.integral_compactness-a1.allard_lemma-a1.cluster_selection-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
