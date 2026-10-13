# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.square_measure-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.square_measure-a1.coord_square_volume-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 5–6 of the parent-supplied proof (the boxes (−r, r)² and [−r, r]² have volume ofReal(2r)·ofReal(2r) = ofReal(4r²); PiLp.volume_preserving_ofLp, Real.volume_pi_Ioo, Real.volume_Icc_pi), isolated as a statement about Lebesgue measure on ℝ² alone.
Notation. ℝ² := Euclid 2 = EuclideanSpace ℝ (Fin 2) with its volume (Lebesgue) measure; for v ∈ ℝ², v₀ := v 0 and v₁ := v 1 are its coordinates. φ := WithLp.ofLp : ℝ² → (Fin 2 → ℝ) is the map forgetting the L² structure, so (φ v) i = v i for i : Fin 2; Fin 2 → ℝ carries the product Lebesgue measure volume. Fix r ∈ ℝ with r ≥ 0.
1. (The coordinate map is measure preserving.) φ is measure preserving from volume on ℝ² to volume on Fin 2 → ℝ (Mathlib PiLp.volume_preserving_ofLp (Fin 2)). Hence volume(φ⁻¹(B)) = volume(B) for every measurable B ⊆ Fin 2 → ℝ (MeasurePreserving.measure_preimage, a measurable set being null-measurable).
2. (The value 4r².) ∏_{i : Fin 2} ofReal(r − (−r)) = ofReal(2r)·ofReal(2r) (Fin.prod_univ_two) = ofReal(2r·2r) (ENNReal.ofReal_mul, which needs 2r ≥ 0, true since r ≥ 0) = ofReal(4r²).
3. (Open square as a preimage.) For t ∈ ℝ, |t| < r ⟺ −r < t < r (abs_lt). The elements of Fin 2 are exactly 0 and 1, so |v₀| < r and |v₁| < r hold iff (φ v) i ∈ Ioo(−r, r) for every i : Fin 2. Thus {v : |v₀| < r ∧ |v₁| < r} = φ⁻¹(B°) with B° := Set.pi univ (fun _ : Fin 2 => Ioo(−r, r)).
4. (Open square.) B° is a product of open intervals, hence measurable (MeasurableSet.univ_pi with measurableSet_Ioo). By steps 1 and 3, volume{v : |v₀| < r ∧ |v₁| < r} = volume(B°) = ∏_{i : Fin 2} ofReal(r − (−r)) (Real.volume_pi_Ioo) = ofReal(4r²) (step 2).
5. (Closed square as a preimage.) For t ∈ ℝ, |t| ≤ r ⟺ −r ≤ t ≤ r (abs_le), and the order on Fin 2 → ℝ is pointwise. So {v : |v₀| ≤ r ∧ |v₁| ≤ r} = φ⁻¹(B̄) with B̄ := Icc (fun _ : Fin 2 => −r) (fun _ => r) ⊆ Fin 2 → ℝ.
6. (Closed square.) B̄ is a closed interval of Fin 2 → ℝ, hence measurable (measurableSet_Icc). By steps 1 and 5, volume{v : |v₀| ≤ r ∧ |v₁| ≤ r} = volume(B̄) = ∏_{i : Fin 2} ofReal(r − (−r)) (Real.volume_Icc_pi) = ofReal(4r²) (step 2). ∎
(No case split on r is needed: for r = 0 the open square is empty and the closed square is {0}, and both computations give ofReal 0 = 0.)

Formalization note (verified during the decomposition check; not part of the mathematical argument). The following single theorem proves exactly this frozen statement. It compiles with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b36630) after `import GMT.Ch07.Submission` only, inside `namespace GMT.Ch07` with the contract opens (`open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `open Poincare.SimonGMT.Chapter06`, `open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)`). It uses no sibling declaration, no import and no helper declaration; `#print axioms` gives exactly propext, Classical.choice and Quot.sound. It follows the numbered steps above and may be used directly as the leaf candidate:
```lean
theorem Submission.idtp_cse_bml_sqm_coord_square_volume : ∀ r : ℝ, 0 ≤ r → volume {v : Euclid 2 | |v 0| < r ∧ |v 1| < r} = ENNReal.ofReal (4 * r ^ 2) ∧ volume {v : Euclid 2 | |v 0| ≤ r ∧ |v 1| ≤ r} = ENNReal.ofReal (4 * r ^ 2) := by
  intro r hr
  have hmp := PiLp.volume_preserving_ofLp (Fin 2)
  have h4 : (∏ _i : Fin 2, ENNReal.ofReal (r - -r)) = ENNReal.ofReal (4 * r ^ 2) := by
    rw [Fin.prod_univ_two, ← ENNReal.ofReal_mul (by linarith)]
    congr 1
    ring
  constructor
  · have hset : {v : Euclid 2 | |v 0| < r ∧ |v 1| < r} =
        WithLp.ofLp ⁻¹' (Set.pi univ fun _ : Fin 2 => Ioo (-r) r) := by
      ext v
      simp [abs_lt, Fin.forall_fin_two]
    rw [hset, hmp.measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet,
      Real.volume_pi_Ioo, h4]
  · have hset : {v : Euclid 2 | |v 0| ≤ r ∧ |v 1| ≤ r} =
        WithLp.ofLp ⁻¹' (Set.Icc (fun _ : Fin 2 => -r) (fun _ => r)) := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, Pi.le_def, Fin.forall_fin_two,
        abs_le]
      tauto
    rw [hset, hmp.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi, h4]
```

## Key steps

1. WithLp.ofLp : Euclid 2 → (Fin 2 → ℝ) is volume preserving (PiLp.volume_preserving_ofLp), so measurable boxes keep their volume under preimage.
2. The open square {|v₀| < r ∧ |v₁| < r} is the preimage of Set.pi univ (fun _ => Ioo (−r) r), and the closed square {|v₀| ≤ r ∧ |v₁| ≤ r} that of Icc (fun _ => −r) (fun _ => r) (abs_lt, abs_le, Fin 2 = {0, 1}).
3. Real.volume_pi_Ioo and Real.volume_Icc_pi give ∏_{i : Fin 2} ofReal(2r) = ofReal(2r)·ofReal(2r) = ofReal(4r²), using r ≥ 0.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c); git -C .lake/packages/{mathlib,simongmt} rev-parse HEAD; cmp snapshot project/GMT/Ch07/Submission.lean with workspace GMT/Ch07/Submission.lean; git rev-parse b4d606db1:GMT/Ch07/Submission.lean vs f7d98547:GMT/Ch07/Submission.lean`
- `python3 scan of dag.json: selected node (depth 5, decomposing), parent idtp_cse_edge_box_mass_limits and its 8 children; lean_statement regex scan (Measure.map, μHE[2], Orthonormal, volume, Set.pi, Ioo, Icc, finrank+span) over all and accepted nodes; duplicate lean_names; reuse precedent nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-10c568d35f/decomposition-v3.json`
- `rg -n 'euclideanHausdorffMeasure_image|theorem euclideanHausdorffMeasure_eq_volume|euclideanHausdorffMeasure_preimage|map_euclideanHausdorffMeasure' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'theorem volume_preserving_ofLp|volume_preserving_toLp|theorem volume_pi_Ioo|theorem volume_Icc_pi|theorem MeasurePreserving.measure_preimage|theorem measure_preimage' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'theorem eq_of_le_of_finrank_eq|theorem finrank_span_eq_card|class Regular \(|theorem Orthonormal.linearIndependent|theorem orthonormal_iff_ite|theorem norm_add_sq_real' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -n 'regular_euclideanHausdorffMeasure_restrict_submodule' -A 30 .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `git cat-file -p ae1d8342b0e070140eb7cdd80292f9370a4dd8e5:GMT/Ch07/Submission.lean (accepted idtp_pc_plane_hausdorff_eq_map; difflib vs b4d606db: +37/-0) and its handoff nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ca4a690a2b/parent-child-handoff.json`
- `name scans for idtp_cse_bml_sqm: grep dag.json; grep -rl run dir; rg -l snapshot; rg -l .lake/packages/simongmt; xargs -P 8 grep -rl --include=*.lean over every .swarm-worktrees/*/gmt-ch07/GMT tree (all ch07 worktrees among the 4272 .swarm-worktrees entries); git for-each-ref (6664 refs at check time) -> 1455 unique GMT/Ch07/Submission.lean blobs | git cat-file --batch | grep -c (0 hits; control grep for the accepted name: 2 hits)`
- `lake env lean /tmp/sqm-decomp-r4t8/check/{Stmts,Child1,Child2,ParentAx,Full}.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-28f1e57df5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-da1a1b47c9/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ca4a690a2b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ca4a690a2b/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-10c568d35f/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/tmp/sqm-decomp-r4t8/check/Stmts.lean`
- `/tmp/sqm-decomp-r4t8/check/Child1.lean`
- `/tmp/sqm-decomp-r4t8/check/Child2.lean`
- `/tmp/sqm-decomp-r4t8/check/ParentAx.lean`
- `/tmp/sqm-decomp-r4t8/check/Full.lean`

The pins match: the snapshot project equals the workspace contract b4d606db, at Mathlib 25730c7c and SimonGMT 2b36630. This node's proof base f7d98547 has the same Submission.lean.

Mathlib supplies every library fact used: Isometry.map_euclideanHausdorffMeasure and EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean), PiLp.volume_preserving_ofLp (Haar/InnerProductSpace.lean:134), Real.volume_pi_Ioo and Real.volume_Icc_pi (Lebesgue/Basic.lean:235,244), MeasurePreserving.measure_preimage, Submodule.eq_of_le_of_finrank_eq, finrank_span_eq_card, orthonormal_iff_ite, norm_add_sq_real, and Measure.Regular, which extends IsFiniteMeasureOnCompacts. SimonGMT supplies regular_euclideanHausdorffMeasure_restrict_submodule (Chapter03/Rectifiable.lean:187), which is inside the frozen import closure.

The DAG has the comparator-accepted idtp_pc_plane_hausdorff_eq_map (candidate ae1d8342), whose type is exactly the general transfer H^n⌞span τ = ι_#L^n. It is reused at a byte-identical type, following the reuse precedent in decomposition 10c568d35f. No accepted declaration covers box volumes in ℝ² or span{a, e} = Q.

The new name idtp_cse_bml_sqm_coord_square_volume is unreserved everywhere at check time. That covers the DAG, the run directory, the snapshot, SimonGMT, Mathlib, the ch07 worktrees and all git-ref Submission.lean blobs.

All types elaborate. The parent follows from the two child types (ParentAx.lean), and complete proofs of both children and of the parent compile with only propext, Classical.choice and Quot.sound.
