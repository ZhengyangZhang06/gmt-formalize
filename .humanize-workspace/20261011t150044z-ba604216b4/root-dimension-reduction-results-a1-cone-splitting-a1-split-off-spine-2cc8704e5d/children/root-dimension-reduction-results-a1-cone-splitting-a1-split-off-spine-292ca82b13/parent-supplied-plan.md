# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_param-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-292ca82b13/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1`
- Child key: `cone_param`
- Declaration: `Submission.dimred_cs_sos_cfs_cone_param`
- Exact Lean type: `∀ (P q : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) (q + 1)) (Y : GeometricCurrentOn (univ : Set (Euclid P)) (q + 1 + 1)) (G : ℕ → Euclid (q + 1) → Euclid P) (A : ℕ → Set (Euclid (q + 1))) (w : ℕ → Euclid (q + 1) → ℤ) (c : ℕ → Euclid (q + 1) → ℝ), IsCompact X.support → (∀ i, ∃ L : NNReal, LipschitzWith L (G i)) → (∀ i, MeasurableSet (A i)) → (∀ i, Measurable (w i)) → (∀ i, Measurable (c i)) → (∀ i, ∀ u ∈ A i, DifferentiableAt ℝ (G i) u) → (∀ i, G i '' A i ⊆ X.support) → (∀ i, IntegrableOn (fun u => (w i u : ℝ)) (A i)) → (∀ i, ∀ u ∈ A i, 0 ≤ c i u ∧ ∀ α : Covector (Euclid P) (q + 1), |α (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1))| ≤ c i u * covectorEuclideanNorm α) → ∑' i, ∫⁻ u in A i, ENNReal.ofReal (|(w i u : ℝ)| * c i u) ≠ ∞ → (∀ γ : TestFormOn (univ : Set (Euclid P)) (q + 1), HasSum (fun i => ∫ u in A i, (w i u : ℝ) * (γ : DifferentialForm (Euclid P) (q + 1)) (G i u) (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1))) (X γ)) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (q + 1 + 1), ∃ η : TestFormOn (univ : Set (Euclid P)) (q + 1), (∀ x ∈ X.support, (η : DifferentialForm (Euclid P) (q + 1)) x = ∫ t in (0 : ℝ)..1, t ^ (q + 1) • ((ω : DifferentialForm (Euclid P) (q + 1 + 1)) (t • x)).curryLeft x) ∧ Y ω = X η) → ∃ (H : ℕ → Euclid (q + 1 + 1) → Euclid P) (B : ℕ → Set (Euclid (q + 1 + 1))) (h : ℕ → Euclid (q + 1 + 1) → ℤ) (c' : ℕ → Euclid (q + 1 + 1) → ℝ), (∀ i, ∃ L : NNReal, LipschitzWith L (H i)) ∧ (∀ i, MeasurableSet (B i)) ∧ (∀ i, Measurable (h i)) ∧ (∀ i, Measurable (c' i)) ∧ (∀ i, IntegrableOn (fun u => (h i u : ℝ)) (B i)) ∧ (∀ i, ∀ u ∈ B i, 0 ≤ c' i u ∧ ∀ α : Covector (Euclid P) (q + 1 + 1), |α (fun a => fderiv ℝ (H i) u (EuclideanSpace.single a 1))| ≤ c' i u * covectorEuclideanNorm α) ∧ ∑' i, ∫⁻ u in B i, ENNReal.ofReal (|(h i u : ℝ)| * c' i u) ≠ ∞ ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (q + 1 + 1), HasSum (fun i => ∫ u in B i, (h i u : ℝ) * (ω : DifferentialForm (Euclid P) (q + 1 + 1)) (H i u) (fun a => fderiv ℝ (H i) u (EuclideanSpace.single a 1))) (Y ω)`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.covector_bounds-a1.curry_le-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
