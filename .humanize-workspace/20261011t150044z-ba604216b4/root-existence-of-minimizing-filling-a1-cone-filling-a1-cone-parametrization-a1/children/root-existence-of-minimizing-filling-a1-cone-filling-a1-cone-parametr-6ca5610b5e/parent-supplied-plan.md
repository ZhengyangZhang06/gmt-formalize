# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_parametrization-a1.piece_weight-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1-cone-parametr-6ca5610b5e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_parametrization-a1`
- Child key: `piece_weight`
- Declaration: `Submission.ecf_cp_piece_weight`
- Exact Lean type: `∀ (k P : ℕ) (F : Euclid k → Euclid P) (A : Set (Euclid k)) (g : Euclid k → ℤ) (G : Euclid (k + 1) → Euclid P) (ρ : ℝ), MeasurableSet A → Measurable g → (∀ u ∈ A, ‖F u‖ ≤ ρ) → (∀ u ∈ A, ∀ t ∈ Ioo (0 : ℝ) 1, (fun a => fderiv ℝ G (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) (EuclideanSpace.single a 1)) = (Fin.cons (F u) (t • fun b => fderiv ℝ F u (EuclideanSpace.single b 1)) : Fin (k + 1) → Euclid P)) → ∫⁻ z in {z : Euclid (k + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid k) ∈ A}, ‖(g (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) : ℝ)‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin (k + 1) => inner ℝ (fderiv ℝ G z (EuclideanSpace.single a 1)) (fderiv ℝ G z (EuclideanSpace.single b 1))))) ≤ ENNReal.ofReal ρ * ∫⁻ u in A, ‖(g u : ℝ)‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin k => inner ℝ (fderiv ℝ F u (EuclideanSpace.single a 1)) (fderiv ℝ F u (EuclideanSpace.single b 1)))))`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1.cyl_fubini-a1`
- `root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_parametrization-a1.gram_cone-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
