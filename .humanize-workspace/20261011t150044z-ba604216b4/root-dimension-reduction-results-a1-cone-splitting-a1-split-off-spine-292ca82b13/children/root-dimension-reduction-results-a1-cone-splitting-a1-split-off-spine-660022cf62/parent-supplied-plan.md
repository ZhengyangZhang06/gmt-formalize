# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_param-a1.cone_map-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-660022cf62/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_param-a1`
- Child key: `cone_map`
- Declaration: `Submission.dimred_cs_sos_cfs_cp_cone_map`
- Exact Lean type: `∀ (P n : ℕ) (G : Euclid n → Euclid P) (L : NNReal) (ρ : ℝ), LipschitzWith L G → ∃ H : Euclid (n + 1) → Euclid P, (∃ K : NNReal, LipschitzWith K H) ∧ ∀ z : Euclid (n + 1), WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 → ‖G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))‖ < ρ → H z = WithLp.ofLp z 0 • G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) ∧ (DifferentiableAt ℝ G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) → (fun b => fderiv ℝ H z (EuclideanSpace.single b 1)) = Fin.cons (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))) (fun a => WithLp.ofLp z 0 • fderiv ℝ G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) (EuclideanSpace.single a 1)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
