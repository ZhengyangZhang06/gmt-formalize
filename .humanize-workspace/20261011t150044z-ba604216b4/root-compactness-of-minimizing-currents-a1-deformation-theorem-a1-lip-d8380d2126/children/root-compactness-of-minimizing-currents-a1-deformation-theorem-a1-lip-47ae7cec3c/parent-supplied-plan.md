# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1.phi_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-47ae7cec3c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1`
- Child key: `phi_bound`
- Declaration: `Submission.cmcdt_lpoh_phi_bound`
- Exact Lean type: `(∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) → (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (N N' k : ℕ) (γ : Covector (Euclid N') (k + 1)) (D : Euclid (N + 1) →L[ℝ] Euclid N') (φ : Covector (Euclid N) k) (a b : ℝ), 0 ≤ b → ‖D (EuclideanSpace.single 0 1)‖ ≤ a → (∀ v : Euclid N, ‖D (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)))‖ ≤ b * ‖v‖) → (∀ v : Fin k → Euclid N, φ v = (γ.compContinuousLinearMap D) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → covectorEuclideanNorm φ ≤ b ^ k * a * covectorEuclideanNorm γ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
