# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.product_support-a1.slice_integral_vanish-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-product-2072ce06f4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.product_support-a1`
- Child key: `slice_integral_vanish`
- Declaration: `Submission.iwl_cr_ci_ps_slice_integral_eq_zero`
- Exact Lean type: `∀ (P m : ℕ) (R : ℝ) (X : GeometricCurrentOn (univ : Set (Eucl P)) m) (η : TestFormOn (univ : Set (Eucl (P + 1))) (m + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl P)) m), X.support ⊆ closedBall 0 R → Disjoint (tsupport (η : DifferentialForm (Eucl (P + 1)) (m + 1))) ((fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) '' (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : Eucl P) R)) → (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl P) (v : Fin m → Eucl P), (φ s : DifferentialForm (Eucl P) m) x v = (η : DifferentialForm (Eucl (P + 1)) (m + 1)) ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i))))) → ∫ s in (0 : ℝ)..1, X (φ s) = 0`

## Sibling prerequisites

- `root.isoperimetric-a1.vanish_off_support-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
