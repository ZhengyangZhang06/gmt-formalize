# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.boundary_variation-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.boundary_variation-a1.mass_disjoint_sum-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 9 of the supplied proof of the selected theorem, where Σ_p V_p ≤ M(∂Q₀) is obtained by gluing near-optimal forms on the pairwise disjoint N_p. This is the summation over faces in Simon Ch. 6, proof of 5.1, after (32) (chapter-06.txt lines 1888–1899). Here the argument is stated for an arbitrary current and an arbitrary finite pairwise disjoint family, with the union W in place of ℝ^P.

Notation. W := ⋃_{i∈s} N_i. |·| := covectorEuclideanNorm. Adm(A) := massAdmissibleOn U n A = {ω ∈ TestFormOn U n : tsupport ω ⊆ A and |ω(x)| ≤ 1 for all x}. M_A(S) := S.massOn A = sSup{ofReal(S ω) : ω ∈ Adm(A)}.

1. Gluing. Let ω_i ∈ Adm(N_i) for i ∈ s, and let ω := Σ_{i∈s} ω_i, a sum in the submodule TestFormOn U n. Its underlying form is Σ_{i∈s} ω_i (Submodule.coe_sum), so ω(x) = Σ_{i∈s} ω_i(x) (Finset.sum_apply). We claim ω ∈ Adm(W) and S(ω) = Σ_{i∈s} S(ω_i).
 (a) S is linear, so S(ω) = Σ_{i∈s} S(ω_i) (map_sum).
 (b) support ω ⊆ ⋃_{i∈s} support ω_i ⊆ ⋃_{i∈s} tsupport ω_i (Finset.sum_fn, Finset.support_sum, subset_tsupport). The last set is a finite union of closed sets, hence closed (isClosed_biUnion_finset). So tsupport ω = closure(support ω) ⊆ ⋃_{i∈s} tsupport ω_i ⊆ ⋃_{i∈s} N_i = W (closure_minimal).
 (c) Fix x. If ω_i(x) = 0 for every i ∈ s, then ω(x) = 0 and |ω(x)| = 0 ≤ 1 (covectorEuclideanNorm_zero). Otherwise pick i₀ ∈ s with ω_{i₀}(x) ≠ 0. Then x ∈ support ω_{i₀} ⊆ tsupport ω_{i₀} ⊆ N_{i₀}. For i ∈ s with i ≠ i₀, ω_i(x) ≠ 0 would give x ∈ N_i in the same way, contradicting N_i ∩ N_{i₀} = ∅. Hence ω(x) = ω_{i₀}(x) (Finset.sum_eq_single) and |ω(x)| ≤ 1.
2. Trivial case. If M_W(S) = ∞, the claim holds (le_top). Assume from now on that M_W(S) ≠ ∞. For i ∈ s we have N_i ⊆ W, so M_{N_i}(S) ≤ M_W(S) (massOn_mono) and M_{N_i}(S) ≠ ∞. Put V_i := M_{N_i}(S).toReal ≥ 0. Then ofReal(V_i) = M_{N_i}(S) (ENNReal.ofReal_toReal).
3. Near-optimal forms. Let η > 0 and i ∈ s. We find ω_i ∈ Adm(N_i) with V_i − η ≤ S(ω_i).
 - If V_i ≤ η, take ω_i := 0. It lies in Adm(N_i), since tsupport 0 = ∅ and |0| = 0 ≤ 1, and S(0) = 0 ≥ V_i − η.
 - If V_i > η, then 0 ≤ V_i − η < V_i = M_{N_i}(S).toReal, so ofReal(V_i − η) < M_{N_i}(S) (ENNReal.ofReal_lt_iff_lt_toReal). By lt_sSup_iff, some ω_i ∈ Adm(N_i) has ofReal(V_i − η) < ofReal(S ω_i). This forces V_i − η < S(ω_i) (ENNReal.ofReal_lt_ofReal_iff').
4. Glue. Choose such ω_i for every i ∈ s (choose). By step 1, ω := Σ_{i∈s} ω_i ∈ Adm(W). So ofReal(S ω) ≤ M_W(S) (le_massOn), and since M_W(S) ≠ ∞, S(ω) ≤ M_W(S).toReal (ENNReal.ofReal_le_iff_le_toReal). Hence
 Σ_{i∈s} V_i − |s|·η = Σ_{i∈s}(V_i − η) ≤ Σ_{i∈s} S(ω_i) = S(ω) ≤ M_W(S).toReal,
 using Finset.sum_le_sum, Finset.sum_sub_distrib, Finset.sum_const and nsmul_eq_mul. So Σ_{i∈s} V_i ≤ M_W(S).toReal + |s|·η.
5. Limit. Let ε > 0. If s = ∅, step 4 with η := 1 gives Σ_{i∈s} V_i ≤ M_W(S).toReal ≤ M_W(S).toReal + ε. Otherwise, step 4 with η := ε/|s| > 0 gives Σ_{i∈s} V_i ≤ M_W(S).toReal + ε. Hence Σ_{i∈s} V_i ≤ M_W(S).toReal (le_of_forall_pos_le_add).
6. Conclusion. Σ_{i∈s} M_{N_i}(S) = Σ_{i∈s} ofReal(V_i) = ofReal(Σ_{i∈s} V_i) ≤ ofReal(M_W(S).toReal) = M_W(S). The second equality uses ENNReal.ofReal_sum_of_nonneg and V_i ≥ 0; the inequality uses ENNReal.ofReal_le_ofReal and step 5; the last equality uses ENNReal.ofReal_toReal. ∎

## Key steps

1. Admissible forms ω_i for the pairwise disjoint N_i have at most one nonzero value at each point. So Σ ω_i is admissible for W = ⋃ N_i, and S(Σ ω_i) = Σ S(ω_i).
2. If M_W(S) = ∞ there is nothing to prove. Otherwise every M_{N_i}(S) is finite; put V_i := M_{N_i}(S).toReal.
3. Choose ω_i ∈ Adm(N_i) with S(ω_i) ≥ V_i − η (the zero form if V_i ≤ η, otherwise lt_sSup_iff) and glue them: Σ V_i − |s|η ≤ M_W(S).toReal.
4. Let η → 0 and convert back to [0, ∞] with ofReal.

## Reference use

### local-project

Queries:
- `cat SNAPSHOT/manifest.json (project_commit b4d606db, mathlib_commit 25730c7c); git -C SNAPSHOT/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d); md5sum GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean (identical)`
- `rg -n -l 'dimred_mbl_dtfrbv|cmcdtfrbv_face_covectors|cmr_cc_det_covector' SNAPSHOT/mathlib/Mathlib SNAPSHOT/project -g '*.lean' (no match); rg -n -l dimred_mbl_dtfrbv_face_neighbourhoods / _massOn_disjoint_sum_le / _face_test_form over SNAPSHOT/project, lake-packages-25730c7c/simongmt and workspace GMT (no match); grep -c of each new name in RUN/dag.json (0)`
- `python3 -I scans of RUN/dag.json: status, candidate_commit, updated_at, depends_on and lean_statement of cmcdtfrbv_face_covectors (accepted, d7f25773, 2026-10-14T01:14:25Z), cmr_cc_det_covector_exists (accepted, fee01ff8) and cmr_cc_det_covector_basis_kronecker (accepted, 00788882); this node (decomposing, attempt 2, 01:29:31Z); the twin cmcdtfr_boundary_variation children (cmcdtfrbv_face_neighbourhoods and cmcdtfrbv_massOn_disjoint_sum_le: comparing at 01:30Z, accepted only after this attempt began; same types as two new children); byte equality of the reused frozen types and of the selected type with the twin type`
- `cat of the face_covectors node files accepted-candidate.json, isolated-comparator-result.json (passed) and lean-audit-v1.json (machine-leaf, comparator_passed, Submission.cmcdtfrbv_face_covectors); python3 -I check that the three reused natural proofs and key steps are verbatim from their parent-child-handoff.json`
- `grep/sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose depth guard, _existing_lean_name_problem, _accepted_checkpoint, _solve_children, _install_parent_supplied_child_handoff early return for accepted children, _solve resume of accepted candidates), store.py (refresh, accepted-status immutability), decomposition_recovery.py, prompts.py DECOMPOSITION_AUDIT, lean_contract.validate_lean_statement; swarm-project.json (max_depth 6, max_children 12, decomposition_attempts 5)`
- `python3 -I contract_scope(GMT/Ch07/Contract.lean, GMT.Ch07.main_theorem) from verifier/gmt-compare.py: open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt); noncomputable section; end`
- `sed/grep of SimonGMT Chapter06 Mass.lean (covectorEuclideanNorm, covectorEuclideanNorm_zero, massAdmissibleOn, GeometricCurrentOn.massOn, .mass, .massOn_mono, .le_massOn), Currents.lean (TestFormOn, GeometricCurrentOn, boundary, tsupport_exteriorDerivative_subset), CurrentLocalEquality.lean (support); grep 'abbrev Euclid' GMT/Ch07/Contract.lean (EuclideanSpace ℝ (Fin P))`
- `rg -n 'theorem exists_contDiff_support_eq_eq_one_iff' (Geometry/Manifold/PartitionOfUnity.lean:789) and 'closure_thickening_subset_cthickening' (Topology/MetricSpace/Thickening.lean:293) in SNAPSHOT/mathlib`
- `sed -n 1835,1900p and 600,625p of book/chapter-06.txt: Simon Ch. 6 §5 (26)–(33) and Remark 2.35, the sources cited in the child proofs`
- `lake env lean on /tmp/dmfrbv2/lean/{Types,Assembly,FN,MD,FTF,FC}.lean on /tmp/dmfrbv2/gen/{TypesV2,AsmV2,FNV2,MDV2,FCV2,FTFV2,E2EV2}.lean, generated by /tmp/dmfrbv2/scripts/gen_lean.py from the exact lean_statement strings of the decomposition and dag.json; and on /tmp/dmfrbv2/gen2/FTFV2NoScope.lean (explicit (⊤ : ℕ∞), no open scoped ContDiff); #print axioms reports only propext, Classical.choice and Quot.sound`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-9ba692d275/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-9ba692d275/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-488f890568/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-488f890568/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-488f890568/lean-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-488f890568/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-coo-498906c61d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-coo-40c536ad5f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/tmp/dmfrbv2/gen/TypesV2.lean`
- `/tmp/dmfrbv2/gen/AsmV2.lean`
- `/tmp/dmfrbv2/gen/FNV2.lean`
- `/tmp/dmfrbv2/gen/MDV2.lean`
- `/tmp/dmfrbv2/gen/FCV2.lean`
- `/tmp/dmfrbv2/gen/FTFV2.lean`
- `/tmp/dmfrbv2/gen/E2EV2.lean`
- `/tmp/dmfrbv2/gen2/FTFV2NoScope.lean`

Pins match: project b4d606db, Mathlib 25730c7c and SimonGMT 2b36630. Submission.lean is byte-identical to the frozen contract. Neither the snapshot project nor Mathlib contains lattice-face neighbourhoods, face test forms or local-mass superadditivity, so these three obligations are new. They get fresh dimred_mbl_dtfrbv_* names, which collide with nothing in the DAG, the snapshot, Mathlib, SimonGMT or the workspace. The twin's cmcdtfrbv_face_neighbourhoods and cmcdtfrbv_massOn_disjoint_sum_le have identical types but were accepted only after this attempt began, so they are not reused. cmcdtfrbv_face_covectors, cmr_cc_det_covector_exists and cmr_cc_det_covector_basis_kronecker are accepted checkpoints whose frozen types are byte-identical to the proposed ones. Their natural proofs are reproduced verbatim. face_covectors became accepted at 01:14:25Z, before this attempt began, so the attempt-1 name objection no longer applies. Every cited Mathlib or SimonGMT name resolves under the frozen imports. The generated type, assembly, leaf and end-to-end files compile with only the standard axioms.
