# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1.homotopy_maps-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-1f53c4c294/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1`
- Child key: `homotopy_maps`
- Declaration: `Submission.dor_lmb_fcdp_homotopy_maps`
- Exact Lean type: `∀ (P : ℕ) (Λ La Lχ : NNReal) (A : ℝ) (a : ℝ → ℝ) (χ : Euclid P → ℝ) (F G : Euclid P → Euclid P), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith La a → (∀ t, |a t| ≤ A) → LipschitzWith Lχ χ → HasCompactSupport χ → (∃ L : NNReal, LipschitzWith L (fun y : Euclid (P + 1) => F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))))) ∧ (ContDiff ℝ 1 a → ContDiff ℝ 1 χ → ∀ Fs Gs : ℕ → Euclid P → Euclid P, (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, ContDiff ℝ 1 (Gs j)) → (∀ j, LipschitzWith Λ (Fs j)) → (∀ j, LipschitzWith Λ (Gs j)) → TendstoUniformly Fs F atTop → TendstoUniformly Gs G atTop → (∀ j, ContDiff ℝ 1 (fun y : Euclid (P + 1) => Fs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (Gs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - Fs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))))) ∧ (∃ L : NNReal, ∀ j, LipschitzWith L (fun y : Euclid (P + 1) => Fs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (Gs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - Fs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))))) ∧ TendstoUniformly (fun j (y : Euclid (P + 1)) => Fs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (Gs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - Fs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) (fun y : Euclid (P + 1) => F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) atTop) ∧ ∀ (F' G' : Euclid P → Euclid P) (W : Set (Euclid P)) (k : ℕ) (ω : DifferentialForm (Euclid P) (k + 1)) (t : ℝ) (x : Euclid P), ContDiff ℝ 1 a → ContDiff ℝ 1 χ → ContDiff ℝ 1 F' → ContDiff ℝ 1 G' → IsOpen W → (∀ z ∈ W, χ z = 1) → (∀ s ∈ Ioo (-1 : ℝ) 2, a s = s) → x ∈ W → t ∈ Ioo (-1 : ℝ) 2 → (((ω ((fun y : Euclid (P + 1) => F' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x) : Fin (P + 1) → ℝ)))).compContinuousLinearMap (fderiv ℝ (fun y : Euclid (P + 1) => F' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x) : Fin (P + 1) → ℝ)))).curryLeft (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ))).compContinuousLinearMap (fderiv ℝ (fun x' : Euclid P => (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x') : Fin (P + 1) → ℝ) : Euclid (P + 1))) x) = ((ω (F' x + t • (G' x - F' x))).curryLeft (G' x - F' x)).compContinuousLinearMap (fderiv ℝ F' x + t • (fderiv ℝ G' x - fderiv ℝ F' x))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
