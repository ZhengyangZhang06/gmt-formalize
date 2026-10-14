# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.estimate-a1.affine_homotopy-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-796242b44f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.estimate-a1`
- Child key: `affine_homotopy`
- Declaration: `Submission.cmcdt_lpo_she_affine_homotopy`
- Exact Lean type: `∀ (N N' : ℕ) (F G : Euclid N → Euclid N'), ContDiff ℝ (⊤ : ℕ∞) F → ContDiff ℝ (⊤ : ℕ∞) G → ∃ H : Euclid (N + 1) → Euclid N', ContDiff ℝ (⊤ : ℕ∞) H ∧ (∀ (t : ℝ) (x : Euclid N), H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) ∧ (∀ (t : ℝ) (x : Euclid N), fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1) = G x - F x) ∧ ∀ (t : ℝ) (x v : Euclid N), fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ F x v + t • (fderiv ℝ G x v - fderiv ℝ F x v)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
