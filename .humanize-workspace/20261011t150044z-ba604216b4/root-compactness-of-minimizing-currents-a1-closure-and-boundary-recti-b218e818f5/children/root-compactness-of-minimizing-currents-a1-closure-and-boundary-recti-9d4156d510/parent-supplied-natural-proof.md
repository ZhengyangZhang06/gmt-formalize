# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.filling-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 3 (V3: a compactly supported IM filling Y of ∂T, by the isoperimetric theorem when n = d + 1 ≥ 2 and by signed segments from a point when n = 1, the total multiplicity being zero by (VO)); Simon Ch. 6, 6.1 (chapter-06.txt lines 1939–1960, isoperimetric theorem) and 8.2 (lines 2297–2330: "the general case of the theorem follows from the special case when ∂T = 0"). Uses the siblings rsd_cmr_support_subset_of_vanish (key support_vanish), cbr_cc_current_algebra (key current_algebra), cbr_cc_segment_current (key segment_current) and cbr_cc_zero_current_finite_sum (key zero_current_sum).
1. spt ∂T ⊆ spt T, and spt ∂T is compact. If η ∈ 𝒟^d(ℝ^P) has tsupport disjoint from spt T, then tsupport(dη) ⊆ tsupport η (tsupport_exteriorDerivative_subset), so ∂T(η) = T(dη) = 0 by (VO). support_vanish with U := ℝ^P and K := spt T (compact) gives spt ∂T ⊆ spt T and spt ∂T compact.
Case d = m + 1 ≥ 1.
2. Z := ∂T ∈ 𝒟_{m+1}(ℝ^P) is integer multiplicity, has compact support (step 1), ∂Z = ∂∂T = 0 (GeometricCurrentOn.boundary_boundary) and M(Z) < ∞. (ISO) with P and m gives c ≥ 1 and an integer multiplicity Y ∈ 𝒟_{m+2}(ℝ^P) = 𝒟_{d+1}(ℝ^P) with ∂Y = Z = ∂T, M(Y) ≤ ofReal(c(2cM(Z))^{1/(m+1)}M(Z)) < ∞, and spt Y ⊆ thickening(r, spt Z) with r := 3√P(2cM(Z))^{1/(m+1)}.
3. spt Y is compact: spt Z is compact, hence bounded, so thickening(r, spt Z) is bounded and its closure C is compact (ℝ^P is proper). If tsupport ω is disjoint from C, it is disjoint from spt Y, so Y(ω) = 0 by (VO); support_vanish with K := C gives that spt Y is compact.
Case d = 0.
4. By step 1 and zero_current_sum (with (MR) and (VO)) applied to the integer multiplicity, compactly supported ∂T ∈ 𝒟_0(ℝ^P), there are a finite F ⊆ spt ∂T and integers m(x) with ∂T(g) = Σ_{x∈F} m(x)g(x)⟨⟩ for every test 0-form g.
5. Total multiplicity zero: Σ_{x∈F} m(x) = 0. Choose ρ > 0 with spt T ⊆ B_ρ(0) (spt T is compact, hence bounded). Let ψ be a smooth bump function with compact support and ψ = 1 on B̄_ρ(0) (ContDiffBump centred at 0 with radii ρ < 2ρ), and let g(y) := constOfIsEmpty(ψ(y)), the 0-form with g(y)⟨⟩ = ψ(y); g is smooth with compact support, so g ∈ 𝒟⁰(ℝ^P). For y ∈ B_ρ(0), ψ = 1 on a neighbourhood of y, so Dψ(y) = 0 and dg(y) = ofSubsingleton(Dψ(y)) = 0 (extDeriv_constOfIsEmpty). Hence the support of dg lies in the closed set ℝ^P ∖ B_ρ(0), so tsupport(dg) is disjoint from B_ρ(0) ⊇ spt T, and ∂T(g) = T(dg) = 0 by (VO). On the other hand F ⊆ spt ∂T ⊆ spt T ⊆ B_ρ(0) by step 1, so g(x)⟨⟩ = 1 for x ∈ F and ∂T(g) = Σ_{x∈F} m(x). Hence Σ_{x∈F} m(x) = 0.
6. Segments. Put a := 0 ∈ ℝ^P. For each x ∈ ℝ^P choose, by segment_current (with (MR)), an integer multiplicity S_x ∈ 𝒟_1(ℝ^P) with ∂S_x(g) = g(x)⟨⟩ − g(a)⟨⟩ for all test 0-forms g, M(S_x) < ∞ and spt S_x ⊆ [a, x].
7. Combination. current_algebra (c), with (IMC)(c), U := ℝ^P (open), ι := ℝ^P, the finite set F, the currents S_x and the integers m(x), gives an integer multiplicity Y ∈ 𝒟_1(ℝ^P) with Y(ω) = Σ_{x∈F} m(x)S_x(ω) for all ω and M(Y) ≤ Σ_{x∈F}|m(x)|M(S_x) < ∞ (a finite sum of finite terms).
8. ∂Y = ∂T: for every test 0-form g, ∂Y(g) = Y(dg) = Σ_{x∈F} m(x)S_x(dg) = Σ_{x∈F} m(x)∂S_x(g) = Σ_{x∈F} m(x)g(x)⟨⟩ − (Σ_{x∈F} m(x))g(a)⟨⟩ = ∂T(g) by steps 4–6; hence ∂Y = ∂T (GeometricCurrentOn.ext).
9. spt Y is compact: C := ⋃_{x∈F}[a, x] is compact, being a finite union of segments, each the continuous image of [0, 1]. If tsupport ω ∩ C = ∅, then tsupport ω ∩ spt S_x = ∅ for each x ∈ F, so S_x(ω) = 0 by (VO) and Y(ω) = 0; support_vanish with K := C gives that spt Y is compact.
10. In both cases Y is integer multiplicity, ∂Y = ∂T, M(Y) < ∞ and spt Y is compact. ∎

## Key steps

1. spt ∂T ⊆ spt T is compact ((VO) and support_vanish).
2. d ≥ 1: (ISO) applied to the cycle ∂T; the filling lies in a bounded thickening, so its support is compact.
3. d = 0: ∂T = Σ m(x)δ_x over a finite F ⊆ spt T (zero_current_sum), and Σ m(x) = 0 by testing with a bump form equal to 1 near spt T and (VO).
4. Y := Σ m(x)[[0, x]] (segment_current, current_algebra (c)) is IM with ∂Y = ∂T, finite mass and compact support.

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
