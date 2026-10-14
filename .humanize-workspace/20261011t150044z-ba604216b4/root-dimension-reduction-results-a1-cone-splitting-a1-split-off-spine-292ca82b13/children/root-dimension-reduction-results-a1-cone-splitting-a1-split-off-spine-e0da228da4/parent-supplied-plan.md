# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_param-a1.piece_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-e0da228da4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_param-a1`
- Child key: `piece_bounds`
- Declaration: `Submission.dimred_cs_sos_cfs_cp_piece_bounds`
- Exact Lean type: `∀ (P n : ℕ) (ρ : ℝ) (G : Euclid n → Euclid P) (H : Euclid (n + 1) → Euclid P) (A : Set (Euclid n)) (w : Euclid n → ℤ) (c : Euclid n → ℝ), Measurable G → MeasurableSet A → Measurable w → Measurable c → IntegrableOn (fun u => (w u : ℝ)) A → (∀ u ∈ A, ‖G u‖ ≤ ρ) → (∀ u ∈ A, 0 ≤ c u ∧ ∀ α : Covector (Euclid P) n, |α (fun a => fderiv ℝ G u (EuclideanSpace.single a 1))| ≤ c u * covectorEuclideanNorm α) → (∀ z : Euclid (n + 1), WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 → (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A → (fun b => fderiv ℝ H z (EuclideanSpace.single b 1)) = Fin.cons (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))) (fun a => WithLp.ofLp z 0 • fderiv ℝ G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) (EuclideanSpace.single a 1))) → IntegrableOn (fun z : Euclid (n + 1) => (w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) : ℝ)) {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A} ∧ (∀ z : Euclid (n + 1), WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 → (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A → 0 ≤ WithLp.ofLp z 0 ^ n * ‖G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))‖ * c (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) ∧ ∀ α : Covector (Euclid P) (n + 1), |α (fun b => fderiv ℝ H z (EuclideanSpace.single b 1))| ≤ WithLp.ofLp z 0 ^ n * ‖G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))‖ * c (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) * covectorEuclideanNorm α) ∧ ∫⁻ z in {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A}, ENNReal.ofReal (|(w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) : ℝ)| * (WithLp.ofLp z 0 ^ n * ‖G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))‖ * c (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))))) ≤ ENNReal.ofReal ρ * ∫⁻ u in A, ENNReal.ofReal (|(w u : ℝ)| * c u)`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1.cyl_fubini-a1`
- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.covector_bounds-a1.curry_le-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
