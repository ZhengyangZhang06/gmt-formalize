# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.cylinder-a1.slice_forms-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-eab28eee1f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.cylinder-a1`
- Child key: `slice_forms`
- Declaration: `Submission.dimred_mbl_dt_lpc_slice_forms`
- Exact Lean type: `((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → (∀ (N k : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)), (∃ η : ℝ → TestFormOn (univ : Set (Euclid N)) k, ∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ η : ℝ → TestFormOn (univ : Set (Euclid N)) k, (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → (∀ (t : ℝ) (x : Euclid N), covectorEuclideanNorm ((η t : DifferentialForm (Euclid N) k) x) ≤ covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))))) ∧ (∀ (s t : ℝ) (x : Euclid N), covectorEuclideanNorm ((η s : DifferentialForm (Euclid N) k) x - (η t : DifferentialForm (Euclid N) k) x) ≤ c * |s - t|) ∧ ∀ t : ℝ, tsupport (η t : DifferentialForm (Euclid N) k) ⊆ {x : Euclid N | (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) ∈ tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1))}) ∧ ∀ (N k : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) k), (∃ β : ℝ → TestFormOn (univ : Set (Euclid N)) k, ∀ (s : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (β s : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∃ γ : ℝ → TestFormOn (univ : Set (Euclid N)) k, ∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (γ t : DifferentialForm (Euclid N) k) x v = fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ ∀ β : ℝ → TestFormOn (univ : Set (Euclid N)) k, (∀ (s : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (β s : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → ∀ (s : ℝ) (x : Euclid N), covectorEuclideanNorm ((β s : DifferentialForm (Euclid N) k) x) ≤ covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))))`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.cone-a1.coeff_lipschitz-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
