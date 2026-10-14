# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1.interior_energy-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-6192900ace/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1`
- Child key: `interior_energy`
- Declaration: `Submission.dorag_ha_lsc_interior_energy`
- Exact Lean type: `∀ (n : ℕ) (R E r : ℝ) (h : Euclid n → ℝ), 0 < r → r < R → 0 ≤ E → ContDiffOn ℝ 2 h (ball (0 : Euclid n) R) → (∀ Φ : Fin n → Euclid n → ℝ, (∀ i, ContDiff ℝ 1 (Φ i)) → (∀ i, HasCompactSupport (Φ i)) → (∀ i, tsupport (Φ i) ⊆ ball (0 : Euclid n) R) → ∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) * Φ i x ≤ Real.sqrt E * Real.sqrt (∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, Φ i x ^ 2)) → ∫ x in ball (0 : Euclid n) r, ‖fderiv ℝ h x‖ ^ 2 ≤ E`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1.grad_norm_sq-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
