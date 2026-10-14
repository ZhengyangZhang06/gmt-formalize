# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.cylinder-a1.restriction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-57af8dc9f1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.cylinder-a1`
- Child key: `restriction`
- Declaration: `Submission.cmcdt_lpo_cyl_restriction_bounds`
- Exact Lean type: `(∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) → (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → (∀ N k : ℕ, ∃ Φ : Covector (Euclid (N + 1)) (k + 1) →L[ℝ] Covector (Euclid N) k, (∀ (γ : Covector (Euclid (N + 1)) (k + 1)) (v : Fin k → Euclid N), Φ γ v = γ (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ ∀ γ : Covector (Euclid (N + 1)) (k + 1), covectorEuclideanNorm (Φ γ) ≤ covectorEuclideanNorm γ) ∧ (∀ N k : ℕ, ∃ Ψ : Covector (Euclid (N + 1)) k →L[ℝ] Covector (Euclid N) k, (∀ (γ : Covector (Euclid (N + 1)) k) (v : Fin k → Euclid N), Ψ γ v = γ (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ ∀ γ : Covector (Euclid (N + 1)) k, covectorEuclideanNorm (Ψ γ) ≤ covectorEuclideanNorm γ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
