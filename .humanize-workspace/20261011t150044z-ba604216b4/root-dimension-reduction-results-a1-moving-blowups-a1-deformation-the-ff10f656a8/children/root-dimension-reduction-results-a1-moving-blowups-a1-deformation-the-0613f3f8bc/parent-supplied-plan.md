# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.smooth_mass-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-0613f3f8bc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1`
- Child key: `smooth_mass`
- Declaration: `Submission.dimred_mbl_dt_lpo_smooth_homotopy_mass`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (N N' k : ℕ) (Λ δ b : ℝ) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (C : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)) (β : TestFormOn (univ : Set (Euclid N')) (k + 1)) (θ : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)), ContDiff ℝ (⊤ : ℕ∞) F → ContDiff ℝ (⊤ : ℕ∞) G → ContDiff ℝ (⊤ : ℕ∞) H → (∀ (t : ℝ) (x : Euclid N), H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → X.mass < ∞ → (∀ x ∈ X.support, ‖fderiv ℝ F x‖ ≤ Λ ∧ ‖fderiv ℝ G x‖ ≤ Λ) → (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (∀ y, covectorEuclideanNorm ((β : DifferentialForm (Euclid N') (k + 1)) y) ≤ b) → (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ X.support, (θ : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = ((β : DifferentialForm (Euclid N') (k + 1)) (H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))))).compContinuousLinearMap (fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))))) → (∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : ℝ → TestFormOn (univ : Set (Euclid N)) k, (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ C ω = ∫ t in (0 : ℝ)..1, X (η t)) → |C θ| ≤ δ * Λ ^ k * b * X.mass.toReal`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.toolkit-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.affine_homotopy-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
