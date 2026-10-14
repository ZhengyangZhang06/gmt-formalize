# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1.suspension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-d2dfefa5bc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1`
- Child key: `suspension`
- Declaration: `Submission.dimred_mbl_dt_lp_imc_suspension`
- Exact Lean type: `∀ (N n : ℕ) (G : Euclid n → Euclid N) (Gh : Euclid (n + 1) → Euclid (N + 1)), (∀ (t : ℝ) (u : Euclid n), Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp (G u)))) → (∀ L : NNReal, LipschitzWith L G → LipschitzWith (max 1 L) Gh) ∧ (∀ (m : ℝ) (A : Set (Euclid n)), (∀ a ∈ A, ∀ a' ∈ A, m * ‖a - a'‖ ≤ ‖G a - G a'‖) → ∀ (t t' : ℝ), ∀ u ∈ A, ∀ u' ∈ A, min 1 m * ‖(WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (n + 1)) - WithLp.toLp 2 (Fin.cons t' (WithLp.ofLp u'))‖ ≤ ‖Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) - Gh (WithLp.toLp 2 (Fin.cons t' (WithLp.ofLp u')))‖) ∧ ∀ (t : ℝ) (u : Euclid n), DifferentiableAt ℝ G u → DifferentiableAt ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) ∧ (∀ (s : ℝ) (w : Euclid n), fderiv ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp w))) = WithLp.toLp 2 (Fin.cons s (WithLp.ofLp (fderiv ℝ G u w)))) ∧ (Injective (fderiv ℝ G u) → Injective (fderiv ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))))) ∧ LinearMap.range (fderiv ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) : Euclid (n + 1) →ₗ[ℝ] Euclid (N + 1)) = Submodule.span ℝ (insert (EuclideanSpace.single 0 1) ((fun v : Euclid N => (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)) : Euclid (N + 1))) '' (LinearMap.range (fderiv ℝ G u : Euclid n →ₗ[ℝ] Euclid N) : Set (Euclid N)))) ∧ Matrix.det (Matrix.of fun i j : Fin (n + 1) => inner ℝ (fderiv ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) (EuclideanSpace.single i 1)) (fderiv ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) (EuclideanSpace.single j 1))) = Matrix.det (Matrix.of fun i j : Fin n => inner ℝ (fderiv ℝ G u (EuclideanSpace.single i 1)) (fderiv ℝ G u (EuclideanSpace.single j 1)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
