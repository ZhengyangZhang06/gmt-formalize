# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_param-a1.piece_action-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-e2ded5a465/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_param-a1`
- Child key: `piece_action`
- Declaration: `Submission.dimred_cs_sos_cfs_cp_piece_action`
- Exact Lean type: `∀ (P n : ℕ) (L : NNReal) (G : Euclid n → Euclid P) (H : Euclid (n + 1) → Euclid P) (A : Set (Euclid n)) (w : Euclid n → ℤ) (ω : TestFormOn (univ : Set (Euclid P)) (n + 1)) (η : DifferentialForm (Euclid P) n), LipschitzWith L H → MeasurableSet A → Measurable w → IntegrableOn (fun u => (w u : ℝ)) A → (∀ z : Euclid (n + 1), WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 → (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A → H z = WithLp.ofLp z 0 • G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) ∧ (fun b => fderiv ℝ H z (EuclideanSpace.single b 1)) = Fin.cons (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))) (fun a => WithLp.ofLp z 0 • fderiv ℝ G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) (EuclideanSpace.single a 1))) → (∀ u ∈ A, η (G u) = ∫ t in (0 : ℝ)..1, t ^ n • ((ω : DifferentialForm (Euclid P) (n + 1)) (t • G u)).curryLeft (G u)) → ∫ u in A, (w u : ℝ) * η (G u) (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) = ∫ z in {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A}, (w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) : ℝ) * (ω : DifferentialForm (Euclid P) (n + 1)) (H z) (fun b => fderiv ℝ H z (EuclideanSpace.single b 1))`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1.cyl_fubini-a1`
- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1.pullback_integrable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
