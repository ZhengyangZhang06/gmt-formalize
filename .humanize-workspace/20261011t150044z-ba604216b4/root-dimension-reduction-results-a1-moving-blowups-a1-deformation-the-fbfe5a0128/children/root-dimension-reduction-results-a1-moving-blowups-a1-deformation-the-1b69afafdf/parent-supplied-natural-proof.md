# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.polyhedral_im-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.polyhedral_im-a1.isometry_image_integral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the supplied proof of the selected node dimred_mbl_dtfr_polyhedral_im (“Change of variables. Φ_p is an isometry, hence a closed embedding and a measurable embedding … F̆_p is Borel; ∫_{F̆_p} h dHᵏ = ∫_{Q₁} h(Φ_p y) dy …; Hᵏ(F̆_p) = vol(Q₁) = 1”). It is stated here for an arbitrary isometry Φ and Borel set A; the parent applies it with Φ = Φ_p and A = Q₁. The same type is frozen in the twin branch (root.compactness_of_minimizing_currents-a1.…polyhedral_im-a1) under the name cmcdtfrpi_isometry_image_integral. That name is reserved there, so this child is declared under the fresh name Submission.dimred_mbl_dtfrpi_isometry_image_integral and proved here.

Notation. Hᵏ := μHE[k], on Euclid P or on Euclid k as indicated; Lᵏ := volume on Euclid k; μ⌞S := μ.restrict S; Φ_#μ := μ.map Φ.

1. Measurable embedding. Euclid k is complete and Φ is an isometry, so Φ is a closed embedding (Isometry.isClosedEmbedding). A closed embedding between Borel spaces is a measurable embedding (Topology.IsClosedEmbedding.measurableEmbedding): Φ is injective and measurable, and it maps Borel sets to Borel sets. Hence Φ(A) is Borel (MeasurableEmbedding.measurableSet_image). This is the first conclusion.
2. Hᵏ = Lᵏ on Euclid k, by EuclideanSpace.euclideanHausdorffMeasure_eq_volume k.
3. Measure of the image. Hausdorff measure is invariant under isometries, for every set: Hᵏ(Φ(A)) = Hᵏ(A) (Isometry.euclideanHausdorffMeasure_image). By step 2, Hᵏ(A) = Lᵏ(A). This is the second conclusion.
4. Push-forward identity: Hᵏ⌞Φ(A) = Φ_#(Lᵏ⌞A) as measures on Euclid P.
 - For a measurable embedding and every set E, (Φ_#μ)⌞E = Φ_#(μ⌞Φ⁻¹(E)) (MeasurableEmbedding.restrict_map). Apply it with μ := Hᵏ on Euclid k and E := Φ(A).
 - Φ_#Hᵏ = Hᵏ⌞range Φ (Isometry.map_euclideanHausdorffMeasure). So the left side is (Hᵏ⌞range Φ)⌞Φ(A) = Hᵏ⌞(Φ(A) ∩ range Φ) (Measure.restrict_restrict; Φ(A) is Borel by step 1), and this is Hᵏ⌞Φ(A) because Φ(A) ⊆ range Φ.
 - On the right side, Φ⁻¹(Φ(A)) = A by injectivity (Set.preimage_image_eq), and Hᵏ⌞A = Lᵏ⌞A by step 2.
5. Change of variables. For a measurable embedding Φ, every measure μ on Euclid k and every function g : Euclid P → ℝ, ∫ g d(Φ_#μ) = ∫ g∘Φ dμ (MeasurableEmbedding.integral_map). No measurability or integrability hypothesis is needed: g is AE-strongly measurable for Φ_#μ exactly when g∘Φ is for μ, integrability transfers in the same way, and otherwise both Bochner integrals are 0. Take μ := Lᵏ⌞A and use step 4: ∫_{Φ(A)} h dHᵏ = ∫ h d(Hᵏ⌞Φ(A)) = ∫ h d(Φ_#(Lᵏ⌞A)) = ∫_A h(Φ(y)) dy. This is the third conclusion.
6. No case distinction is needed. For k = 0, Euclid 0 is a single point and the same lemmas apply verbatim. ∎

Lean note (checked). A proof of exactly this type compiles in the comparator scope (import GMT.Ch07.Submission, the contract's opens, namespace GMT.Ch07), with axioms propext, Classical.choice and Quot.sound only:
 - hemb := hΦ.isClosedEmbedding.measurableEmbedding, and hemb.measurableSet_image.mpr hA;
 - rw [hΦ.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume k];
 - the identity μHE[k].restrict (Φ '' A) = (volume.restrict A).map Φ, from hemb.restrict_map μHE[k] (Φ '' A) rewritten with hΦ.map_euclideanHausdorffMeasure, Measure.restrict_restrict, Set.inter_eq_left.mpr (Set.image_subset_range _ _), Set.preimage_image_eq _ hemb.injective and the volume identity;
 - finally rw [that identity, hemb.integral_map].
This was re-checked under the declaration name Submission.dimred_mbl_dtfrpi_isometry_image_integral.

## Key steps

1. An isometry from the complete space Euclid k is a closed, hence measurable, embedding, so Φ(A) is Borel.
2. Hᵏ is isometry-invariant and equals Lebesgue measure on Euclid k, so Hᵏ(Φ(A)) = vol(A).
3. Hᵏ⌞Φ(A) = Φ_#(vol⌞A), from map_euclideanHausdorffMeasure, MeasurableEmbedding.restrict_map, injectivity and restrict_restrict.
4. MeasurableEmbedding.integral_map gives ∫_{Φ(A)} h dHᵏ = ∫_A h∘Φ dy for every h.

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
