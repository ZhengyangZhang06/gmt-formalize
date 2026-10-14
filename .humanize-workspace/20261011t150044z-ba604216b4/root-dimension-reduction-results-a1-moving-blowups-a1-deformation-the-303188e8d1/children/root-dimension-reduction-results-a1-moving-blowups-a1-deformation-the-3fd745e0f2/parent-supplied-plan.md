# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1.shell_series-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-3fd745e0f2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1`
- Child key: `shell_series`
- Declaration: `Submission.dimred_mbl_dtsd_sh_shell_series`
- Exact Lean type: `(∀ (P n : ℕ), (∀ (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) n), IsClosed E → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) E → X ω = 0) → X.support ⊆ E) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) n, IsClosed X.support) ∧ (∀ A B : GeometricCurrentOn (univ : Set (Euclid P)) n, (A - B).support ⊆ A.support ∪ B.support) ∧ (0 : GeometricCurrentOn (univ : Set (Euclid P)) n).support = ∅ ∧ (∀ A : GeometricCurrentOn (univ : Set (Euclid P)) (n + 1), A.boundary.support ⊆ A.support)) → (∀ (P d : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U d) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P d) (E V : Set (Euclid P)), (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) d, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U d, X ω = ∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) d) x) ∂μ) → X.massOn V ≤ μ (E ∩ V)) → ∀ (P k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k) (A Y : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) k) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k) (d : Euclid P → ℝ) (r : ℕ → ℝ), IsFiniteMeasure μ → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) k, |ξ x α| ≤ covectorEuclideanNorm α) → μ X.supportᶜ = 0 → Continuous d → StrictAnti r → Tendsto (fun j => μ {x | d x < r j}) atTop (𝓝 0) → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) → (∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k), A j ω = ∫ x in {x | d x < r j}, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Y 0 ω = X ω - A 0 ω) → (∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k), Y (j + 1) ω = A j ω - A (j + 1) ω) → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Y 0 ω = ∫ x in {x | r 0 ≤ d x}, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) ∧ (∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k), Y (j + 1) ω = ∫ x in {x | r (j + 1) ≤ d x ∧ d x < r j}, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) k, HasSum (fun j => Y j ω) (X ω)) ∧ (∀ j, (Y j).support ⊆ X.support ∩ {x | r j ≤ d x}) ∧ (∀ j, (A j).support ⊆ X.support) ∧ (Y 0).mass ≤ μ univ ∧ (∀ j, (Y (j + 1)).mass ≤ μ {x | d x < r j})`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.mass_representation-a1.eval_mass_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
