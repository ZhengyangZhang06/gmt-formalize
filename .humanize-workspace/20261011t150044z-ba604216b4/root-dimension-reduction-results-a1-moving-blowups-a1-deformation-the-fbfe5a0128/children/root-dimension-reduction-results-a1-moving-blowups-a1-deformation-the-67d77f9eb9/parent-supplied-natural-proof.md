# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.polyhedral_im-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.polyhedral_im-a1.local_plane_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4(iii) of the supplied proof of dimred_mbl_dtfr_polyhedral_im. There, for 0 < r < δ/R, the blow-ups of the carrier agree with V_p on B(0, R), so r ↦ ∫_{η_{x,r}(C)} f dHᵏ is eventually equal to ∫_{V_p} f dHᵏ along 𝓝[>] 0. Here it is stated for an arbitrary set M and subspace V; the local hypothesis is exactly what step 4(ii) provides for the carrier. It generalizes SimonGMT's hasApproximateTangentSpaceAt_submodule (Poincare/SimonGMT/Chapter03/Rectifiable.lean), which is the case M = V, x ∈ V.

Notation. η_{x,r}(y) := blowUpMap x r y = r⁻¹ • (y − x), and Hⁿ := μHE[n] on Euclid P. By definition, HasApproximateTangentSpaceAt n M x V means: finrank ℝ V = n, and for every f ∈ C_c(Euclid P, ℝ) the function r ↦ ∫_{η_{x,r}(M)} f dHⁿ tends to ∫_V f dHⁿ along 𝓝[>] 0.

1. finrank ℝ V = n is a hypothesis. Fix f ∈ C_c(Euclid P, ℝ) for the rest of the proof.
2. A ball outside which f vanishes. tsupport f is compact, hence bounded, so tsupport f ⊆ B̄(0, R₀) for some R₀ ∈ ℝ. Put R := max(R₀, 0) + 1. Then R > 0 and R > R₀. If ‖y‖ ≥ R, then y ∉ B̄(0, R₀) ⊇ tsupport f, so f(y) = 0 (image_eq_zero_of_notMem_tsupport). Hence f vanishes outside the open ball B := B(0, R).
3. Localization. For every set S ⊆ Euclid P, measurable or not, ∫_S f dHⁿ = ∫_{B∩S} f dHⁿ. Indeed B is open, hence Borel, so (Hⁿ⌞S)⌞B = Hⁿ⌞(B ∩ S) (Measure.restrict_restrict). Since f = 0 off B, ∫ f d((Hⁿ⌞S)⌞B) = ∫ f d(Hⁿ⌞S) (setIntegral_eq_integral_of_forall_compl_eq_zero).
4. Claim: if r > 0 and rR < δ (equivalently 0 < r < δ/R), then B ∩ η_{x,r}(M) = B ∩ V.
 (⊆) Let y ∈ B with y = r⁻¹(z − x) for some z ∈ M. Then ‖y‖ = r⁻¹‖z − x‖ < R, so ‖z − x‖ < rR < δ, i.e. dist(z, x) < δ. By the hypothesis, z ∈ M gives z − x ∈ V. Since V is a subspace, y = r⁻¹(z − x) ∈ V.
 (⊇) Let y ∈ B ∩ V and put z := x + r y. Then z − x = r y ∈ V, and dist(z, x) = ‖r y‖ = r‖y‖ < rR < δ, so z ∈ M by the hypothesis. Also η_{x,r}(z) = r⁻¹(r y) = y because r ≠ 0. So y ∈ η_{x,r}(M).
5. For every r with 0 < r < δ/R, steps 3, 4 and 3 again give
 ∫_{η_{x,r}(M)} f dHⁿ = ∫_{B∩η_{x,r}(M)} f dHⁿ = ∫_{B∩V} f dHⁿ = ∫_V f dHⁿ.
6. Since δ/R > 0, the interval (0, δ/R) belongs to 𝓝[>] 0 (Ioo_mem_nhdsGT). By step 5, r ↦ ∫_{η_{x,r}(M)} f dHⁿ is eventually equal along 𝓝[>] 0 to the constant ∫_V f dHⁿ, so it tends to that constant (Filter.tendsto_congr' with tendsto_const_nhds). Since f was arbitrary, HasApproximateTangentSpaceAt n M x V holds. ∎ No measurability of M is used, and the case n = 0, V = {0} needs no special treatment.

Lean note (checked). A proof of exactly this type, following steps 1–6, compiles in the comparator scope with axioms propext, Classical.choice and Quot.sound only.
 - blowUpMap lives in Poincare.SimonGMT.Chapter03, which the contract does not open, so write Poincare.SimonGMT.Chapter03.blowUpMap. It satisfies blowUpMap x r y = r⁻¹ • (y − x) by rfl: unfold it, then use norm_smul, abs_inv, abs_of_pos and inv_mul_lt_iff₀.
 - R₀ comes from f.hasCompactSupport.isBounded.subset_closedBall 0.
 - Localization: rw [← Measure.restrict_restrict Metric.isOpen_ball.measurableSet, setIntegral_eq_integral_of_forall_compl_eq_zero hfz].
 - Limit: (Filter.tendsto_congr' _).2 tendsto_const_nhds, with filter_upwards [Ioo_mem_nhdsGT _].

## Key steps

1. tsupport f is compact, so f = 0 outside B(0, R) for some R > 0.
2. For 0 < r < δ/R, B(0,R) ∩ η_{x,r}(M) = B(0,R) ∩ V: |z − x| = r|η_{x,r}(z)| < δ, then apply the local hypothesis in both directions.
3. Restricting to the Borel ball does not change ∫ f, so ∫_{η_{x,r}(M)} f dHⁿ = ∫_V f dHⁿ for all small r > 0.
4. The function is eventually constant along 𝓝[>] 0, which gives the limit; finrank V = n is a hypothesis.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json (project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git -C SNAP/project rev-parse HEAD and git -C SNAP/mathlib rev-parse HEAD (both match); python3 -I read of lake-manifest.json (mathlib 25730c7c, simongmt 2b3663083f3f); cmp SNAP/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `rg -c 'dtfrpi|isometry_image_integral|local_plane_tangent|coord_plane_orientation|face_union_local_plane|finite_piece_imrep' -g '*.lean' SNAP/project GMT lake-packages-25730c7c/simongmt (no match, exit 1; positive control rg -c IMRep finds 12 hits in each contract file); the same pattern with rg -l over SNAP/mathlib/Mathlib (no match, exit 1)`
- `python3 -I scans of RUN/dag.json (2181 nodes): no lean_name equals any dimred_mbl_dtfrpi_* name, and there are no duplicate lean_names. Twin statuses: cmcdtfrpi_isometry_image_integral, _coord_plane_orientation and _finite_piece_imrep accepted; _local_plane_tangent comparing; _face_union_local_plane rlcr-lean. Selected node: depth 5, status decomposing, depends_on face_geometry-a1. grep -rl --include=*.json dimred_mbl_dtfrpi RUN/nodes: only this node's own decomposition-v1.json`
- `grep -n of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint, decomposition loop) and lean_contract.py (validate_lean_statement, applied to all five child statements); python3 -I replay of verifier/gmt-compare.py contract_scope against GMT/Ch07/Contract.lean`
- `python3 -I/cat of this node's parent-child-handoff.json and attempt-1 decomposition-v1.json, and of the twin node's decomposition-v1.json and decomposition-audit-v1.json (nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-9de237faed)`
- `rg -n on SNAP/mathlib/Mathlib for Isometry.euclideanHausdorffMeasure_image, Isometry.map_euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean), integral_biUnion_finset (Integral/Bochner/Set.lean) and lintegral_biUnion_finset (Integral/Lebesgue/Basic.lean); rg -n in SimonGMT Chapter03/Rectifiable.lean (CountablyRectifiable, countablyRectifiable_range, HasApproximateTangentSpaceAt, hasApproximateTangentSpaceAt_submodule) and Chapter06/Forms.lean, Currents.lean (Covector, TestFormOn)`
- `grep -n of book/chapter-06.txt for 'evident' and sed -n 1895,1930p (Simon Ch. 6 §5: M(P) = Σ|β_F|; 'the fact that P, R are integer multiplicity if T is should be evident')`
- `lake env lean /tmp/dmpi3-lean/Types.lean; lake env lean /tmp/dmpi3-lean/FinalE2E.lean; lake env lean /tmp/dmpi3-lean/Inst.lean (Lean v4.35.0-rc3 toolchain)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-fbfe5a0128/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-fbfe5a0128/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-9de237faed/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-9de237faed/decomposition-audit-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/dmpi3-lean/Types.lean`
- `/tmp/dmpi3-lean/FinalE2E.lean`
- `/tmp/dmpi3-lean/Inst.lean`

Pins match: project b4d606db, Mathlib 25730c7c and SimonGMT 2b36630. The snapshot contract equals the workspace contract, which equals Submission.lean.

Neither the snapshot nor Mathlib nor SimonGMT contains a lattice-face IM or mass result, so these obligations are new. Mathlib and SimonGMT do supply every tool the child proofs cite: isometry invariance and push-forward of μHE, μHE = volume on Euclid k, biUnion integrals and lintegrals, CountablyRectifiable and HasApproximateTangentSpaceAt.

Attempt 1 was rejected because it reused the twin's cmcdtfrpi_isometry_image_integral, which the runtime reports as reserved by the twin's active branch. This attempt reuses no cmcdtfrpi_* declaration. All five children get fresh dimred_mbl_dtfrpi_* names. None appears in any of the 2181 DAG lean_names, in any other node file, or in the snapshot, workspace, SimonGMT or Mathlib.

Lean checks, re-run under the fresh names:
- All seven challenge types elaborate in the replayed comparator scope: the five children, FG and the selected type.
- All five children are proved.
- The assembly proves the exact selected type from the five child types plus FG.
- Every child target and the assembly use only propext, Classical.choice and Quot.sound. The parent target additionally uses only the face_geometry stand-in.
- ContinuousAdd (MultiVector P k) fails to synthesize, which is why finite_piece_imrep uses a list fold for the orientation. The rfl checks and all cited lemma names resolve.
