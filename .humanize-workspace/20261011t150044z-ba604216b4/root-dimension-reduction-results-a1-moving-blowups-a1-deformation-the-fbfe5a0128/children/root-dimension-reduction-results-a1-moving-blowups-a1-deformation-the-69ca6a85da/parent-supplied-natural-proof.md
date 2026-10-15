# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.polyhedral_im-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.polyhedral_im-a1.finite_piece_imrep-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3–6 of the supplied proof of dimred_mbl_dtfr_polyhedral_im: the triple (C, θ, ξ), its IMRep fields, the splitting of the action integral over the disjoint pieces, and the computation of R.measure. Here they are stated for an arbitrary finite family of disjoint pieces. The parent instantiates it with the open faces F̆_p = Φ_p((0,1)^k), m_p = |β_p|, ξ_p = sign(β_p) e_p and G_p = Φ_p. The contract's IMRep encodes Simon, Ch. 6, Definition 3.1, and IMRep.action encodes 6.3.1 (‡).

Notation. Hᵏ := μHE[k] on Euclid P, and C := ⋃_{q∈S} F_q.

1. Carrier. C is Borel, as a finite union of Borel sets (Finset.measurableSet_biUnion). C ⊆ U because each F_q ⊆ U.
2. Uniqueness of the piece. If p, q ∈ S, q ≠ p and x ∈ F_p, then x ∉ F_q, by the disjointness hypothesis.
3. Multiplicity. Let θ(x) := Σ_{q∈S} 1_{F_q}(x) · m_q ∈ ℕ, the sum of the indicators of the F_q with constant values m_q.
 - θ is measurable: each summand is the indicator of a Borel set with a constant value, and a finite sum of measurable ℕ-valued functions is measurable (Finset.measurable_sum).
 - θ(x) = m_p for x ∈ F_p with p ∈ S: by step 2 every other summand vanishes (Finset.sum_eq_single).
 - Hence θ > 0 on C, since every point of C lies in some F_p with m_p > 0.
4. Orientation. List S as p₁, …, p_N (S.toList). Define ξ(x) := ξ_{p_i} for the least i with x ∈ F_{p_i}, and ξ(x) := 0 if x ∉ C. Formally, ξ(x) is the right fold over the list of (q, acc) ↦ (if x ∈ F_q then ξ_q else acc), starting from 0.
 - By induction on the list, ξ is strongly measurable: the empty fold is constant, and each step is an if-then-else on a Borel set between a constant and a strongly measurable function (StronglyMeasurable.ite). So ξ is AE-strongly measurable for Hᵏ⌞C.
 - ξ(x) = ξ_p whenever x ∈ F_p and p ∈ S, by step 2 and induction on the list: every entry q ≠ p has x ∉ F_q, and the entry p returns ξ_p.
 By disjointness this ξ is the same function as the supplied proof's Σ_{q∈S} 1_{F_q} ξ_q; the fold only changes how it is written. In Lean the sum route through Finset.stronglyMeasurable_sum needs ContinuousAdd (MultiVector P k), and that instance does not synthesize in the frozen environment (checked).
5. Countable rectifiability.
 - With the list p₁, …, p_N, define F_j := G_{p_{j+1}} for j < N, and F_j := the constant map 0 for j ≥ N. Each F_j is Lipschitz, by hypothesis or because it is constant.
 - Every x ∈ C lies in some F_p ⊆ range G_p, and p = p_{j+1} for some j < N. So C ⊆ M₀ ∪ ⋃_j range F_j with M₀ := ∅, and Hᵏ(∅) = 0.
 This is CountablyRectifiable k C. (Equivalently: countablyRectifiable_range for each G_p, then countablyRectifiable_iUnion and CountablyRectifiable.mono, as in the supplied proof.)
6. Total weight. The F_p (p ∈ S) are pairwise disjoint and Borel, so ∫⁻_C θ dHᵏ = Σ_{p∈S} ∫⁻_{F_p} θ dHᵏ (lintegral_biUnion_finset). On F_p, θ = m_p by step 3, so ∫⁻_{F_p} θ dHᵏ = m_p Hᵏ(F_p) (setLIntegral_congr_fun, lintegral_const, Measure.restrict_apply_univ). Hence ∫⁻_C θ dHᵏ = Σ_{p∈S} m_p Hᵏ(F_p), which is finite because every Hᵏ(F_p) < ∞ (ENNReal.sum_ne_top, ENNReal.mul_ne_top).
7. Local integrability. For every compact K ⊆ U, ∫⁻_{C∩K} θ dHᵏ ≤ ∫⁻_C θ dHᵏ < ∞ (lintegral_mono_set).
8. Orients. Let x ∈ C, so x ∈ F_p for some p ∈ S. The hypothesis gives Q with HasApproximateTangentSpaceAt k C x Q and IsUnitOrientationOf ξ_p Q, and ξ(x) = ξ_p by step 4. So the orients condition holds at every point of C. Since C is Borel, it holds Hᵏ⌞C-a.e. (ae_restrict_of_forall_mem).
9. Steps 1 and 3–8 verify every field of IMRep U k for R := (C, θ, ξ).
10. Action. Let ω ∈ 𝒟ᵏ(U), and write ω also for the underlying form. It is C^∞, hence continuous, with compact support. By definition, R.action(ω) = ∫_C θ(x) · ξ(x)(ω(x)) dHᵏ(x).
 - For p ∈ S let g_p(x) := m_p · ξ_p(ω(x)). g_p is continuous, since ξ_p is a continuous linear functional. Its support lies in the support of ω, because ξ_p(0) = 0, so g_p has compact support.
 - Hᵏ⌞F_p is a finite measure, hence finite on compact sets, so g_p is integrable for it (Continuous.integrable_of_hasCompactSupport).
 - On F_p the integrand θ(x)ξ(x)(ω(x)) equals g_p(x), by steps 3 and 4. Since F_p is Borel, the integrand is integrable on F_p (IntegrableOn.congr_fun).
 - The Bochner integral is additive over finitely many pairwise disjoint Borel sets (integral_biUnion_finset). So R.action(ω) = Σ_{p∈S} ∫_{F_p} θ ξ(ω) dHᵏ = Σ_{p∈S} ∫_{F_p} m_p ξ_p(ω(x)) dHᵏ = Σ_{p∈S} m_p ∫_{F_p} ξ_p(ω(x)) dHᵏ(x) (setIntegral_congr_fun, integral_const_mul).
11. Mass measure. R.measure = (Hᵏ⌞C).withDensity θ. So R.measure(Euclid P) = ∫⁻ θ d(Hᵏ⌞C) = ∫⁻_C θ dHᵏ = Σ_{p∈S} m_p Hᵏ(F_p), by withDensity_apply, Measure.restrict_univ and step 6. ∎ If S = ∅, then C = ∅, θ = 0 and ξ = 0: every field holds trivially, and both identities read 0 = 0.

Lean note (checked). A proof of exactly this type (about 150 lines, following steps 1–11) compiles in the comparator scope with axioms propext, Classical.choice and Quot.sound only.
 - Use classical. Take θ := fun x => ∑ q ∈ S, (F q).indicator (fun _ => m q) x, with Finset.measurable_sum S (fun q hq => measurable_const.indicator (hFm q hq)).
 - Take ξf := fun x => S.toList.foldr (fun q acc => if x ∈ F q then ξ q else acc) 0. Prove a list-induction lemma for StronglyMeasurable.ite (hl a List.mem_cons_self) stronglyMeasurable_const ih, and one for the value ξ p.
 - Rectifiability witness: ⟨∅, measure_empty, fun j => if h : j < L.length then G (L.get ⟨j, h⟩) else fun _ => 0, _, _⟩, using List.get_mem, List.mem_iff_get and Finset.mem_toList.
 - Build R with the structure literal { carrier := C, mult := θ, orient := ξf, … }. The two goals then follow by show/defeq: show ∫ x in C, ((θ x : ℕ) : ℝ) * ξf x (ω x) ∂μHE[k] = _ and show ((μHE[k].restrict C).withDensity _) univ = _.
 - Integrability on F p: provide the instance IsFiniteMeasure ((μHE[k]).restrict (F p)) via Measure.restrict_apply_univ, then use Continuous.integrable_of_hasCompactSupport with hωcs.mono, where ω.2.1.1.continuous and ω.2.1.2 give continuity and compact support of ω.

## Key steps

1. Carrier C = ⋃ F_p is Borel and contained in U. It is countably k-rectifiable via the Lipschitz maps G_p, padded with constant maps and M₀ = ∅.
2. θ = Σ m_q 1_{F_q} and ξ = ξ_p on F_p (list fold of if-then-else). By disjointness θ = m_p > 0 and ξ = ξ_p on F_p; both are (strongly) measurable.
3. The orients condition holds at every point of C by hypothesis, hence a.e. on the Borel set C.
4. The lintegral splits over the disjoint pieces: ∫⁻_C θ = Σ m_p Hᵏ(F_p) < ∞, which gives local integrability and R.measure(Euclid P).
5. The action splits the same way: action = Σ m_p ∫_{F_p} ξ_p(ω), since each integrand is continuous with compact support on a finite-measure piece.

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
