# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.cylinder-a1.slice_operator-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-7bc1408dee/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.cylinder-a1`
- Child key: `slice_operator`
- Declaration: `Submission.cmcdt_lpo_cyl_slice_operator`
- Exact Lean type: `(∀ (N k : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ tsupport (η : DifferentialForm (Euclid N) k) ⊆ {x : Euclid N | ∃ t ∈ Icc (0 : ℝ) 1, (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) ∈ tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1))}) → (∀ (N k : ℕ) (α : Covector (Euclid N) k) (f : ℝ → Covector (Euclid N) k) (c : ℝ), Continuous f → (∀ v : Fin k → Euclid N, α v = ∫ t in (0 : ℝ)..1, f t v) → (∀ t ∈ Icc (0 : ℝ) 1, covectorEuclideanNorm (f t) ≤ c) → covectorEuclideanNorm α ≤ c) → (∀ N k : ℕ, ∃ Φ : Covector (Euclid (N + 1)) (k + 1) →L[ℝ] Covector (Euclid N) k, (∀ (γ : Covector (Euclid (N + 1)) (k + 1)) (v : Fin k → Euclid N), Φ γ v = γ (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ ∀ γ : Covector (Euclid (N + 1)) (k + 1), covectorEuclideanNorm (Φ γ) ≤ covectorEuclideanNorm γ) → ∀ N k : ℕ, ∃ S : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1) →ₗ[ℝ] TestFormOn (univ : Set (Euclid N)) k, (∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (x : Euclid N) (v : Fin k → Euclid N), (S ω : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ (∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), tsupport (S ω : DifferentialForm (Euclid N) k) ⊆ {x : Euclid N | ∃ t ∈ Icc (0 : ℝ) 1, (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) ∈ tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1))}) ∧ ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (c : ℝ), (∀ y : Euclid (N + 1), covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) (k + 1)) y) ≤ c) → ∀ x : Euclid N, covectorEuclideanNorm ((S ω : DifferentialForm (Euclid N) k) x) ≤ c`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
