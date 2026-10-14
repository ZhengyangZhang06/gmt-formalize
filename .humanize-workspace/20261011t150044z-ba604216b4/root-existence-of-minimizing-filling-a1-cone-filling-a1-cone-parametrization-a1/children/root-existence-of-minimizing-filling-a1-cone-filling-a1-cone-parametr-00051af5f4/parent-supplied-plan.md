# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_parametrization-a1.cone_map-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1-cone-parametr-00051af5f4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_parametrization-a1`
- Child key: `cone_map`
- Declaration: `Submission.ecf_cp_cone_map`
- Exact Lean type: `∀ (k P : ℕ) (F : Euclid k → Euclid P) (A : Set (Euclid k)) (ρ : ℝ), 0 < ρ → (∃ K : NNReal, LipschitzWith K F) → (∀ u ∈ A, DifferentiableAt ℝ F u) → (∀ u ∈ A, ‖F u‖ < ρ) → ∃ G : Euclid (k + 1) → Euclid P, (∃ K : NNReal, LipschitzWith K G) ∧ ∀ u ∈ A, ∀ t ∈ Ioo (0 : ℝ) 1, G (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) = t • F u ∧ (fun a => fderiv ℝ G (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) (EuclideanSpace.single a 1)) = (Fin.cons (F u) (t • fun b => fderiv ℝ F u (EuclideanSpace.single b 1)) : Fin (k + 1) → Euclid P)`

## Sibling prerequisites

- `root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_parametrization-a1.ball_retraction-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
