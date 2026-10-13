# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.cylinder-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-c9dc9edd39/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1`
- Child key: `cylinder`
- Declaration: `Submission.cmcdt_lpo_cylinder`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → ∃ (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact (cyl N k X).support ∧ (cyl N k X).mass < ∞ ∧ (cyl N k X).boundary.mass < ∞ ∧ (cyl N k X).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) ∧ (∀ (N k : ℕ) (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → cyl N k (X - Y) = cyl N k X - cyl N k Y) ∧ ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = X η`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.slice-a1`
- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.toolkit-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
