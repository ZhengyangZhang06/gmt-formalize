# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.isp_sub-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 7 (V4(o)). The slice currents T⌞{f<t}, (∂T)⌞{f<t}, Y⌞{f<t}, (∂Y)⌞{f<t} of the parent's step 0(i) are obtained here from (SL), which asserts their existence. Notation: E_t := {f < t}.
1. Representations. Apply (REP) with U := ℝ^P to T, ∂T, Y and ∂Y (they have locally finite mass). This gives (μ_T, ξ_T), (μ_{∂T}, ξ_{∂T}), (μ_Y, ξ_Y), (μ_{∂Y}, ξ_{∂Y}) with measures finite on compact sets, a.e. strongly measurable fields with |ξ(x)(α)| ≤ |α| for all x (hence a.e.), and T(ω) = ∫ξ_T(ω)dμ_T, ∂T(η) = ∫ξ_{∂T}(η)dμ_{∂T}, Y(ω) = ∫ξ_Y(ω)dμ_Y, ∂Y(η) = ∫ξ_{∂Y}(η)dμ_{∂Y}. These are admissible representations in the sense of the integer slice property.
2. Let (μ, ξ), (μ', ξ') be admissible representations of T − Y and ∂(T − Y), and let f be L-Lipschitz; E_t is Borel for every t because f is continuous.
3. The integer slice property of T, applied to (μ_T, ξ_T), (μ_{∂T}, ξ_{∂T}), f, L, gives a null set N_T such that for t ∉ N_T every pair of currents satisfying the slice formulas for these representations has integer multiplicity ∂A − B; likewise the property of Y gives a null set N_Y. N := N_T ∪ N_Y is null.
4. (SL) with U := ℝ^P, k := d, applied to T with (μ_T, ξ_T), (μ_{∂T}, ξ_{∂T}), f, L (its hypotheses hold by step 1), gives currents A^T_t, B^T_t with A^T_t(ω) = ∫_{E_t}ξ_T(ω)dμ_T and B^T_t(η) = ∫_{E_t}ξ_{∂T}(η)dμ_{∂T} for every t; likewise (SL) applied to Y gives A^Y_t, B^Y_t.
5. Linearity of restrictions. For every ω ∈ 𝒟^{d+1}(ℝ^P), ∫ξ_T(ω)dμ_T = T(ω) = (T − Y)(ω) + Y(ω) = ∫ξ(ω)dμ + ∫ξ_Y(ω)dμ_Y. Hence (RU) (k := d + 1, U := ℝ^P, triples (μ_T, ξ_T), (μ, ξ), (μ_Y, ξ_Y), whose hypotheses hold by step 1 and admissibility) with B := E_t gives ∫_{E_t}ξ_T(ω)dμ_T = ∫_{E_t}ξ(ω)dμ + ∫_{E_t}ξ_Y(ω)dμ_Y. For every η ∈ 𝒟^d(ℝ^P), ∂T(η) = T(dη) = (T − Y)(dη) + Y(dη) = ∂(T − Y)(η) + ∂Y(η), so (RU) with k := d and the triples (μ_{∂T}, ξ_{∂T}), (μ', ξ'), (μ_{∂Y}, ξ_{∂Y}) gives ∫_{E_t}ξ_{∂T}(η)dμ_{∂T} = ∫_{E_t}ξ'(η)dμ' + ∫_{E_t}ξ_{∂Y}(η)dμ_{∂Y}.
6. Fix t ∉ N and currents A, B with A(ω) = ∫_{E_t}ξ(ω)dμ and B(η) = ∫_{E_t}ξ'(η)dμ' for all test forms. By step 5, A(ω) = A^T_t(ω) − A^Y_t(ω) and B(η) = B^T_t(η) − B^Y_t(η). Hence for every η, (∂A − B)(η) = A(dη) − B(η) = [A^T_t(dη) − B^T_t(η)] − [A^Y_t(dη) − B^Y_t(η)], i.e. ∂A − B = (∂A^T_t − B^T_t) − (∂A^Y_t − B^Y_t) (GeometricCurrentOn.ext).
7. By step 3, applied to the pairs (A^T_t, B^T_t) and (A^Y_t, B^Y_t), both brackets are integer multiplicity, so ∂A − B is integer multiplicity by (IMC)(c). Since N is null and (μ, ξ), (μ', ξ'), f were arbitrary, T − Y has the integer slice property. ∎

## Key steps

1. (REP) gives admissible representations of T, ∂T, Y, ∂Y; the integer slice properties of T and Y apply to them outside a null set.
2. (SL) provides slice currents of T and of Y for every t.
3. (RU) turns T = (T − Y) + Y and ∂T = ∂(T − Y) + ∂Y into the same identities for integrals over {f < t}.
4. Hence ∂A − B = (∂A^T_t − B^T_t) − (∂A^Y_t − B^Y_t), which is integer multiplicity by (IMC)(c).

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); read GMT/Ch07/Contract.lean (IMRep, IMRep.action/measure/Represents, IsIntegerMultiplicity, Sub instance, boundaryMassOn, CompactlyContained)`
- `python3 scan of dag.json: frozen lean_statement of the selected node and of the siblings restrict_unique, convergence_tools, isoperimetric, slice_limit, cycle_im; search of accepted reusable declarations (rsd_cmr_support_subset_of_vanish, dtc_imrep_current, rsd_isIntegerMultiplicity_int_combination, dor_imrep_massOn_eq_measure_and_support, dor_zdm_imrep_zero_structure, regcomp_covector_eval_orthonormal_le, dtc_point_current); lean_name collision check (no name with prefix cbr_cc_; the two reused names map only to accepted nodes with byte-identical lean_statement); 153 existing cross-branch reuse edges`
- `grep -n '_existing_lean_name_problem|_solve_children|_install_parent_supplied_child_handoff|_accepted_checkpoint' /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py; sed -n 1,80p speculation.py (prerequisites of a node = its children + depends_on; accepted theorems may be reused by Lean name under a different parent)`
- `grep in snapshot mathlib/Mathlib for: euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_singleton, Isometry.map_euclideanHausdorffMeasure, Isometry.euclideanHausdorffMeasure_image, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, integral_withDensity_eq_integral_smul, restrict_withDensity, restrict_restrict, withDensity_absolutelyContinuous, AEStronglyMeasurable.mono_ac, ae_lt_top, liminf_le_limsup, limsup_le_iSup, integral_eq_sub_of_hasDerivAt, extDeriv_apply, extDeriv_constOfIsEmpty, Filter.EventuallyEq.extDeriv_eq, ContinuousAlternatingMap.apply, constOfIsEmpty, ofSubsingleton, setIntegral_eq_of_subset_of_ae_sdiff_eq_zero, setIntegral_finset, integral_biUnion_finset, integrableOn_singleton_iff, sum_measure_singleton, Infinite.exists_subset_card_eq, Isometry.isClosedEmbedding, MeasurableEmbedding.integral_map, Measure.restrict_map, finrank_span_singleton, PiLp.norm_apply_le, segment_eq_image`
- `read lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean and Chapter03/Rectifiable.lean (GeometricCurrentOn, boundary, boundary_boundary, massOn/massAdmissibleOn, le_massOn, massOn_mono, WeaklyConvergesOn.massOn_le_liminf, WeaklyConvergesOn.boundary, zeroRegion/support, tsupport_exteriorDerivative_subset, CountablyRectifiable, countablyRectifiable_range, countablyRectifiable_of_measure_zero, blowUpMap, HasApproximateTangentSpaceAt)`
- `python3 -I: verifier/lean_contract.py validate_lean_statement on all 8 child statements (pass); verifier/gmt-compare.py contract_scope (replay: open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt); noncomputable section)`
- `lake env lean /tmp/cc-decomp-k7/lean/{Types,Assembly,Fill,Isp,Sub,Alg,Zero,Seg}.lean with #print axioms (Types: 8 child types elaborate; Assembly: frozen node type from 8 child types + 5 sibling types; the other six: each new child from its hypotheses and declared sibling types; all report propext, Classical.choice, Quot.sound)`
- `sed -n on /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt: 195,215p (2.2), 295,320p (2.11-2.14), 730,770p (3.1-3.2), 860,870p (3.10), 1230,1250p (4.5), 1935,1962p (6.1), 2280,2480p (8.2-8.3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b218e818f5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b218e818f5/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-localize-a1-imrep-current-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/speculation.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/SumMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/cc-decomp-k7/lean/Types.lean`
- `/tmp/cc-decomp-k7/lean/Assembly.lean`
- `/tmp/cc-decomp-k7/lean/Fill.lean`
- `/tmp/cc-decomp-k7/lean/Isp.lean`
- `/tmp/cc-decomp-k7/lean/Sub.lean`
- `/tmp/cc-decomp-k7/lean/Alg.lean`
- `/tmp/cc-decomp-k7/lean/Zero.lean`
- `/tmp/cc-decomp-k7/lean/Seg.lean`

Snapshot findings:
- The workspace Contract.lean is the frozen contract, and the pinned snapshot (project b4d606d, mathlib 25730c7c) supplies every Mathlib/SimonGMT lemma cited in the child proofs. SimonGMT has no slicing, filling, segment-current or zero-current structure results, which justifies the split.
- Two accepted declarations fit exactly and are reused by Lean name with byte-identical frozen types: `rsd_cmr_support_subset_of_vanish` (accepted, candidate commit present) and `dtc_imrep_current` (accepted). The runtime reuses such accepted nodes without a new worker.
- The new names (prefix `cbr_cc_`) collide with no DAG declaration.
- Children may use only their own children and depends_on, so the parent's dependency statements (REP, MR, IMC, SL, VO) and the sibling statements (MM from `cbr_measure_convergence_tools`, RU from `cbr_setIntegral_eq_of_integral_eq`, ISO from `cbr_isoperimetric_filling`) are passed verbatim as hypotheses. This node can discharge them, because these siblings are in its depends_on.

Lean validation:
- All 8 statements pass the verifier's lexical check and elaborate in the replayed scope.
- The frozen node type is proved in Lean from the 8 child types plus the 5 sibling types, without sorry.
- Each new child is proved in Lean from its hypotheses and its declared sibling types.
- Every check reports only the axioms propext, Classical.choice and Quot.sound.
