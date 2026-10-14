# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1.duality_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-87b6fe48ce/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1`
- Child key: `duality_bound`
- Declaration: `Submission.dorag_ha_lsc_duality_bound`
- Exact Lean type: `∀ (n : ℕ) (R E : ℝ) (u : ℕ → Euclid n → ℝ) (c : ℕ → ℝ) (W h : Euclid n → ℝ) (Φ : Fin n → Euclid n → ℝ), (∀ j, ∃ L : NNReal, LipschitzWith L (u j)) → (∀ j, ∫ x in ball (0 : Euclid n) R, ‖fderiv ℝ (u j) x‖ ^ 2 ≤ E) → MemLp W 2 (volume.restrict (ball (0 : Euclid n) R)) → Tendsto (fun j => ∫ x in ball (0 : Euclid n) R, (u j x - c j - W x) ^ 2) atTop (𝓝 0) → ContDiffOn ℝ 1 h (ball (0 : Euclid n) R) → (∀ᵐ x ∂(volume.restrict (ball (0 : Euclid n) R)), h x = W x) → (∀ i, ContDiff ℝ 1 (Φ i)) → (∀ i, HasCompactSupport (Φ i)) → (∀ i, tsupport (Φ i) ⊆ ball (0 : Euclid n) R) → ∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) * Φ i x ≤ Real.sqrt E * Real.sqrt (∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, Φ i x ^ 2)`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1.grad_norm_sq-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1.ibp_lipschitz-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1.ibp_c1_ball-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
