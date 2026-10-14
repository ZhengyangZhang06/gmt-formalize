# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.compact_im_param-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-414a1a5f66/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1`
- Child key: `compact_im_param`
- Declaration: `Submission.dimred_cs_sos_cfs_compact_im_param`
- Exact Lean type: `∀ (P n : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) n), IsIntegerMultiplicity X → IsCompact X.support → ∃ R : IMRep (univ : Set (Euclid P)) n, R.Represents X ∧ R.carrier ⊆ X.support ∧ R.measure univ ≠ ∞ ∧ ∃ (G : ℕ → Euclid n → Euclid P) (A : ℕ → Set (Euclid n)) (w : ℕ → Euclid n → ℤ) (c : ℕ → Euclid n → ℝ), (∀ i, ∃ L : NNReal, LipschitzWith L (G i)) ∧ (∀ i, MeasurableSet (A i)) ∧ (∀ i, Measurable (w i)) ∧ (∀ i, Measurable (c i)) ∧ (∀ i, ∀ u ∈ A i, DifferentiableAt ℝ (G i) u) ∧ (∀ i, G i '' A i ⊆ X.support) ∧ (∀ i, IntegrableOn (fun u => (w i u : ℝ)) (A i)) ∧ (∀ i, ∀ u ∈ A i, 0 ≤ c i u ∧ ∀ α : Covector (Euclid P) n, |α (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1))| ≤ c i u * covectorEuclideanNorm α) ∧ ∑' i, ∫⁻ u in A i, ENNReal.ofReal (|(w i u : ℝ)| * c i u) ≠ ∞ ∧ ∀ γ : TestFormOn (univ : Set (Euclid P)) n, HasSum (fun i => ∫ u in A i, (w i u : ℝ) * (γ : DifferentialForm (Euclid P) n) (G i u) (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1))) (X γ)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.vanish_off_support-a1`
- `root.compactness_of_minimizing_currents-a1.mass_equals_rep_measure-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
