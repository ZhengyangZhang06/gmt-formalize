# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.polyhedral_im-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.polyhedral_im-a1.face_union_local_plane-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1 and 4(ii) of the supplied proof of dimred_mbl_dtfr_polyhedral_im: the open faces F̆_p are pairwise disjoint, and C ∩ B(x, δ) = Π_p ∩ B(x, δ). The isometry and separation facts come from the antecedent (FG). (FG) is verbatim the frozen type of Submission.dimred_mbl_dtfr_face_geometry, the selected node's resolved sibling dependency; the parent discharges (FG) with that declaration.

Notation. For p = (ι, b): Φ_p(y) := WithLp.toLp 2 b + Σ_j y_j • e_{ι(j)} for y ∈ Euclid k, with e_i := EuclideanSpace.single i 1. Also Q₁ := {y : 0 < y_i < 1 for all i}, F̆_p := Φ_p(Q₁), C := ⋃_{q∈S} F̆_q and V_p := span_ℝ{e_{ι(j)} : j ∈ Fin k}. Every p ∈ S has a strictly increasing first component.

0. Facts from (FG), applied at (P, k). For pairs p, q whose first components are strictly increasing:
 (iso) dist(Φ_p y, Φ_p y') = dist(y, y') for all y, y' ∈ Euclid k;
 (sep) if p ≠ q, y ∈ Q₁ and y' ∈ [0,1]^k, then 1 ≤ dist(Φ_p y, Φ_q y'), or min(y_j, 1 − y_j) ≤ dist(Φ_p y, Φ_q y') for some j.
1. Part (a), disjointness. Let p ≠ q in S, and suppose w ∈ F̆_p ∩ F̆_q, say w = Φ_p(t) = Φ_q(t') with t, t' ∈ Q₁. Since Q₁ ⊆ [0,1]^k, (sep) applies to (p, q, t, t'). But dist(Φ_p t, Φ_q t') = dist(w, w) = 0. The first alternative gives 1 ≤ 0, which is false. The second gives min(t_j, 1 − t_j) ≤ 0 for some j, which is false because 0 < t_j < 1. So F̆_p ∩ F̆_q = ∅.
2. Part (b), choice of δ. Fix p = (ι, b) ∈ S and t ∈ Q₁, and let x := Φ_p(t). Let D be the finite set {1} ∪ {min(t_j, 1 − t_j) : j ∈ Fin k}; it is nonempty because it contains 1. Put δ := min D. Every element of D is positive, so δ > 0. Also δ ≤ 1, and δ ≤ min(t_j, 1 − t_j) for each j. (For k = 0, D = {1} and δ = 1.)
 Now let z ∈ Euclid P with dist(z, x) < δ. We show z ∈ C ⟺ z − x ∈ V_p.
3. (⇒) Suppose z ∈ C, so z = Φ_q(t') for some q ∈ S and t' ∈ Q₁.
 - If q ≠ p, apply (sep) to (p, q, t, t'); this is allowed since t' ∈ Q₁ ⊆ [0,1]^k. It gives 1 ≤ dist(x, z), or min(t_j, 1 − t_j) ≤ dist(x, z) for some j. But dist(x, z) = dist(z, x) < δ, with δ ≤ 1 and δ ≤ min(t_j, 1 − t_j). So both alternatives are impossible.
 - Hence q = p. Then z − x = Φ_p(t') − Φ_p(t) = Σ_j (t'_j − t_j) e_{ι(j)}, because the constant toLp(b) cancels. This is a linear combination of the e_{ι(j)}, so z − x ∈ V_p (Submodule.mem_span_range_iff_exists_fun, with coefficients t'_j − t_j).
4. (⇐) Suppose z − x ∈ V_p.
 - V_p is spanned by the finite family (e_{ι(j)})_{j ∈ Fin k}, so there is c : Fin k → ℝ with Σ_j c_j e_{ι(j)} = z − x (Submodule.mem_span_range_iff_exists_fun).
 - Let t' := t + toLp(c) ∈ Euclid k, so t'_j = t_j + c_j. Then Φ_p(t') = toLp(b) + Σ_j t_j e_{ι(j)} + Σ_j c_j e_{ι(j)} = x + (z − x) = z.
 - By (iso), dist(t', t) = dist(Φ_p t', Φ_p t) = dist(z, x) < δ. A coordinate distance is at most the Euclidean distance (PiLp.dist_apply_le), so |c_j| = |t'_j − t_j| ≤ dist(t', t) < δ ≤ min(t_j, 1 − t_j) for each j.
 - Hence t'_j = t_j + c_j > t_j − min(t_j, 1 − t_j) ≥ 0, and t'_j < t_j + min(t_j, 1 − t_j) ≤ 1. So t' ∈ Q₁ and z = Φ_p(t') ∈ F̆_p. Since p ∈ S, z ∈ C.
5. Steps 3 and 4 prove the equivalence for every z with dist(z, x) < δ. This completes part (b). ∎

Lean note (checked). A proof of exactly this type compiles in the comparator scope with axioms propext, Classical.choice and Quot.sound only.
 - Start with intro FG P k S hS and obtain ⟨-, FGpq⟩ := FG P k.
 - Image-membership hypotheses arrive beta-unreduced, e.g. (fun y => …) t' = (fun y => …) t; use beta_reduce at them before rewriting.
 - δ := (insert 1 (Finset.univ.image fun j => min (t j) (1 - t j))).min' (Finset.insert_nonempty _ _), with Finset.lt_min'_iff and Finset.min'_le.
 - In (⇒), close the q = p case with Submodule.mem_span_range_iff_exists_fun, sub_smul, Finset.sum_sub_distrib and abel.
 - In (⇐), set t' := t + WithLp.toLp 2 c. Coordinates: t' j = t j + c j by PiLp.add_apply and PiLp.toLp_apply. Then |c j| < δ from PiLp.dist_apply_le t' t j, and finish with abs_lt and linarith.

## Key steps

1. From (FG): each face map is an isometry, and an open face is separated from every other closed face (distance ≥ 1 or ≥ min(t_j, 1 − t_j)).
2. Disjointness: a common point would have distance 0 from itself, which contradicts separation.
3. δ := min({1} ∪ {min(t_j, 1 − t_j)}) > 0.
4. ⇒: a nearby point of another face contradicts separation, so z lies on the same face and z − x = Σ (t'_j − t_j) e_{ι(j)} ∈ V_p.
5. ⇐: write z − x = Σ c_j e_{ι(j)}. By the isometry, |c_j| ≤ |z − x| < δ, so t + c ∈ (0,1)^k and z = Φ_p(t + c) ∈ C.

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
