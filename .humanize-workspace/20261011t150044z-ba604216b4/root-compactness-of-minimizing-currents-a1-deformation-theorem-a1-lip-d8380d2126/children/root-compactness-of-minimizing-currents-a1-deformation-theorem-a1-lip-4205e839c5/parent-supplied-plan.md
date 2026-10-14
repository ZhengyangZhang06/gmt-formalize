# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1.interp_calculus-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-4205e839c5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1`
- Child key: `interp_calculus`
- Declaration: `Submission.cmcdt_lpoh_interp_calculus`
- Exact Lean type: `∀ (N N' : ℕ) (f g : Euclid N → Euclid N'), ContDiff ℝ (⊤ : ℕ∞) f → ContDiff ℝ (⊤ : ℕ∞) g → ∃ h : Euclid (N + 1) → Euclid N', ContDiff ℝ (⊤ : ℕ∞) h ∧ (∀ (t : ℝ) (x : Euclid N), h (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = f x + t • (g x - f x)) ∧ (∀ (t : ℝ) (x : Euclid N), fderiv ℝ h (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1) = g x - f x) ∧ (∀ (t : ℝ) (x v : Euclid N), fderiv ℝ h (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ f x v + t • (fderiv ℝ g x v - fderiv ℝ f x v)) ∧ ∀ (t : ℝ) (x : Euclid N), ‖fderiv ℝ h (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))‖ ≤ ‖g x - f x‖ + ‖fderiv ℝ f x‖ + |t| * (‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
