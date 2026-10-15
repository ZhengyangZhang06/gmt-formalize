# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_parametrization-a1.piece_integral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1-cone-parametr-a4431a9e11/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_parametrization-a1`
- Child key: `piece_integral`
- Declaration: `Submission.ecf_cp_piece_integral`
- Exact Lean type: `∀ (k P : ℕ) (F : Euclid k → Euclid P) (A : Set (Euclid k)) (g : Euclid k → ℤ) (G : Euclid (k + 1) → Euclid P), MeasurableSet A → Measurable g → IntegrableOn (fun u => (g u : ℝ)) A → (∃ K : NNReal, LipschitzWith K G) → (∀ u ∈ A, ∀ t ∈ Ioo (0 : ℝ) 1, G (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) = t • F u ∧ (fun a => fderiv ℝ G (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) (EuclideanSpace.single a 1)) = (Fin.cons (F u) (t • fun b => fderiv ℝ F u (EuclideanSpace.single b 1)) : Fin (k + 1) → Euclid P)) → Measurable (fun z : Euclid (k + 1) => g (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))) ∧ IntegrableOn (fun z : Euclid (k + 1) => (g (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) : ℝ)) {z : Euclid (k + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid k) ∈ A} ∧ ∀ ω : DifferentialForm (Euclid P) (k + 1), Continuous ω → HasCompactSupport ω → ∫ z in {z : Euclid (k + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid k) ∈ A}, (g (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) : ℝ) * ω (G z) (fun a => fderiv ℝ G z (EuclideanSpace.single a 1)) = ∫ u in A, (g u : ℝ) * ∫ t in (0 : ℝ)..1, t ^ k * ω (t • F u) (Fin.cons (F u) (fun b => fderiv ℝ F u (EuclideanSpace.single b 1)))`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1.cyl_fubini-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
