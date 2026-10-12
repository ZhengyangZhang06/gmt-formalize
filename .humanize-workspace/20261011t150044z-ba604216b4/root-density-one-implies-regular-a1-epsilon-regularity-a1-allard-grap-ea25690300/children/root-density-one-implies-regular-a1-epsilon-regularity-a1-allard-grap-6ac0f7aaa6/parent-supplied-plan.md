# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.weyl_lemma-a1.glue-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-6ac0f7aaa6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.weyl_lemma-a1`
- Child key: `glue`
- Declaration: `Submission.dorag_ha_weyl_glue`
- Exact Lean type: `∀ (n : ℕ) (R : ℝ) (F : ℝ → Euclid n → ℝ), 0 < R → (∀ ε : ℝ, 0 < ε → ε < R → ∀ m : ℕ, ContDiffOn ℝ m (F ε) (ball (0 : Euclid n) (R - ε))) → (∀ ε : ℝ, 0 < ε → ε < R → ∀ y ∈ ball (0 : Euclid n) (R - ε), ∑ i : Fin n, iteratedFDeriv ℝ 2 (F ε) y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → (∀ (ε δ : ℝ) (x : Euclid n), 0 < ε → 0 < δ → ‖x‖ + ε + δ < R → F ε x = F δ x) → ∃ h : Euclid n → ℝ, (∀ m : ℕ, ContDiffOn ℝ m h (ball (0 : Euclid n) R)) ∧ (∀ y ∈ ball (0 : Euclid n) R, ∑ i : Fin n, iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) ∧ ∀ x ∈ ball (0 : Euclid n) R, ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε x = h x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
