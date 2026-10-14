# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.weyl_lemma-a1.ae_tendsto-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-81df29144e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.weyl_lemma-a1`
- Child key: `ae_tendsto`
- Declaration: `Submission.dorag_ha_weyl_ae_tendsto`
- Exact Lean type: `∀ (n : ℕ) (f : Euclid n → ℝ) (C : ℝ) (φ : ℝ → Euclid n → ℝ), 0 < n → Integrable f → (∀ ε : ℝ, 0 < ε → Continuous (φ ε)) → (∀ ε : ℝ, 0 < ε → ∀ y : Euclid n, ε ≤ ‖y‖ → φ ε y = 0) → (∀ ε : ℝ, 0 < ε → ∀ y : Euclid n, |φ ε y| ≤ C / ε ^ n) → (∀ ε : ℝ, 0 < ε → ∫ y, φ ε y = 1) → ∀ᵐ x ∂(volume : Measure (Euclid n)), Tendsto (fun ε => ∫ y, f y * φ ε (x - y)) (𝓝[>] (0 : ℝ)) (𝓝 (f x))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
