# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.estimate-a1.slice_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-a394fe28f8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.estimate-a1`
- Child key: `slice_bound`
- Declaration: `Submission.cmcdt_lpo_she_slice_bound`
- Exact Lean type: `(∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) → (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (N N' m : ℕ) (σ : DifferentialForm (Euclid (N + 1)) (m + 1)) (x : Euclid N) (α : Covector (Euclid N) m) (Λ δ c : ℝ), Continuous σ → (∀ v : Fin m → Euclid N, α v = ∫ t in (0 : ℝ)..1, σ (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → (∀ t ∈ Icc (0 : ℝ) 1, ∃ (γ : Covector (Euclid N') (m + 1)) (u : Euclid N') (A : Euclid N →L[ℝ] Euclid N'), ‖A‖ ≤ Λ ∧ ‖u‖ ≤ δ ∧ covectorEuclideanNorm γ ≤ c ∧ ∀ v : Fin m → Euclid N, σ (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = γ (Fin.cons u (fun i => A (v i)))) → covectorEuclideanNorm α ≤ Λ ^ m * δ * c`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
