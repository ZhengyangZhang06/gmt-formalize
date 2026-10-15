# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1.product_imrep-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-985aabc0e9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1`
- Child key: `product_imrep`
- Declaration: `Submission.dor_lmb_fcdp_product_imrep`
- Exact Lean type: `∀ (P k : ℕ) (R : IMRep (univ : Set (Euclid P)) k), R.measure univ ≠ ∞ → ∃ R' : IMRep (univ : Set (Euclid (P + 1))) (k + 1), R'.measure univ ≠ ∞ ∧ (∀ S : Set (Euclid P), MeasurableSet S → μHE[k] (R.carrier \ S) = 0 → μHE[k + 1] (R'.carrier \ ((fun p : ℝ × Euclid P => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (P + 1) → ℝ) : Euclid (P + 1))) '' (Icc (0 : ℝ) 1 ×ˢ S))) = 0) ∧ ∀ β : DifferentialForm (Euclid (P + 1)) (k + 1), Continuous β → (∃ C : ℝ, ∀ y, ‖β y‖ ≤ C) → R'.action β = R.action (fun x => ∫ t in (0 : ℝ)..1, ((β (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x) : Fin (P + 1) → ℝ) : Euclid (P + 1))).curryLeft (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ))).compContinuousLinearMap (fderiv ℝ (fun x' : Euclid P => (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x') : Fin (P + 1) → ℝ) : Euclid (P + 1))) x))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1.cylinder-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
