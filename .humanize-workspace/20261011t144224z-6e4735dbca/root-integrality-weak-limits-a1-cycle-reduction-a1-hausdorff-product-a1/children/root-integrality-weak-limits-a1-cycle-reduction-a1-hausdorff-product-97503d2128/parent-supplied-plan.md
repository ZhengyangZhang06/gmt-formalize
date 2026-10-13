# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1.lift_gram_det-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-97503d2128/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1`
- Child key: `lift_gram_det`
- Declaration: `Submission.iwl_cr_hp_lift_gram_det`
- Exact Lean type: `∀ (P m : ℕ) (G : Eucl m → Eucl P) (Gt : Eucl (m + 1) → Eucl (P + 1)) (w : Eucl (m + 1)) (b : Eucl m), (∀ v : Eucl (m + 1), Gt v = (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons (EuclideanSpace.equiv (Fin (m + 1)) ℝ v 0) (EuclideanSpace.equiv (Fin P) ℝ (G ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ v))))))) → b = (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ w)) → DifferentiableAt ℝ G b → (Matrix.of fun i j : Fin (m + 1) => inner ℝ (fderiv ℝ Gt w (EuclideanSpace.single i 1)) (fderiv ℝ Gt w (EuclideanSpace.single j 1))).det = (Matrix.of fun i j : Fin m => inner ℝ (fderiv ℝ G b (EuclideanSpace.single i 1)) (fderiv ℝ G b (EuclideanSpace.single j 1))).det`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
