# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.affine_homotopy-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-5cefc36dc8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1`
- Child key: `affine_homotopy`
- Declaration: `Submission.dimred_mbl_dt_lpo_affine_homotopy`
- Exact Lean type: `(∀ (N N' : ℕ) (F G : Euclid N → Euclid N'), ContDiff ℝ (⊤ : ℕ∞) F → ContDiff ℝ (⊤ : ℕ∞) G → ∃ H : Euclid (N + 1) → Euclid N', ContDiff ℝ (⊤ : ℕ∞) H ∧ ∀ (t : ℝ) (x : Euclid N), H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) ∧ ∀ (N N' : ℕ) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (t : ℝ) (x : Euclid N), DifferentiableAt ℝ F x → DifferentiableAt ℝ G x → DifferentiableAt ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) → (∀ (s : ℝ) (z : Euclid N), H (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp z))) = F z + s • (G z - F z)) → fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1) = G x - F x ∧ (∀ v : Euclid N, fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ F x v + t • (fderiv ℝ G x v - fderiv ℝ F x v)) ∧ ‖fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))‖ ≤ ‖G x - F x‖ + ‖fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
