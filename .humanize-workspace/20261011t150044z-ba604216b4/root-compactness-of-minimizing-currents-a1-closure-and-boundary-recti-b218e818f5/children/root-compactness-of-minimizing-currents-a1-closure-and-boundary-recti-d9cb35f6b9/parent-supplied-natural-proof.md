# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.segment_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 3, case n = 1 (the segment currents [[x₀, x]]); Simon Ch. 6, 2.2 (chapter-06.txt lines 196–208: the current [[M]] of an oriented submanifold) and 3.1 (lines 733–753). Uses the siblings rsd_cmr_support_subset_of_vanish (key support_vanish), dtc_imrep_current (key imrep_current) and cbr_cc_current_algebra (key current_algebra), parts (a) and (b). (Unlike the parent, a = b is allowed; then S = 0.)
Case a = b.
1. Take S := 0. It is integer multiplicity by current_algebra (a); ∂0(g) = 0 = g(a)⟨⟩ − g(a)⟨⟩; current_algebra (b) with A = B = C = 0 and p = q = 0 gives M(0) = M_{ℝ^P}(0) = 0 < ∞; and 0 vanishes on every test form, so support_vanish (U := ℝ^P, K := {a}) gives spt 0 ⊆ {a} = [a, a] (segment_same).
Case a ≠ b.
2. Parametrization. Let ℓ := |b − a| > 0, τ := ℓ⁻¹(b − a) (so |τ| = 1) and φ(u) := a + uτ (u ∈ ℝ). φ is an isometry ℝ → ℝ^P (|φ(u) − φ(v)| = |u − v|), hence a closed embedding and a measurable embedding (Isometry.isClosedEmbedding, IsClosedEmbedding.measurableEmbedding); φ(0) = a and φ(ℓ) = b. Put I := φ((0, ℓ)), the open segment. I is Borel (the image of a Borel set under a measurable embedding), and I ⊆ [a, b] because φ(u) = a + (u/ℓ)(b − a) with u/ℓ ∈ [0, 1] (segment_eq_image').
3. H¹ on I. On ℝ, H¹ = μHE[1] is Lebesgue measure (InnerProductSpace.euclideanHausdorffMeasure_eq_volume, finrank ℝ ℝ = 1). For the isometry φ the push-forward of H¹ is H¹⌞φ(ℝ) (Isometry.map_euclideanHausdorffMeasure); restricting to I (Measure.restrict_map, and φ⁻¹(I) = (0, ℓ) by injectivity) gives H¹⌞I = φ_#(L¹⌞(0, ℓ)). Consequently H¹(I) = ℓ (Isometry.euclideanHausdorffMeasure_image, Real.volume_Ioo) and ∫_I h dH¹ = ∫_{(0,ℓ)} h(a + uτ) du for every function h (MeasurableEmbedding.integral_map).
4. Orientation. Let ζ₀ be the 1-vector α ↦ α(τ), i.e. ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ => τ), and Q := span{τ}, a line (finrank_span_singleton). ζ₀ is a unit orientation of Q: the one-element family (τ) is orthonormal (|τ| = 1), its span is Q, and ζ₀(α) = α(τ) (IsUnitOrientationOf, first alternative).
5. Approximate tangent line at every point of I. Let x = φ(s₀) with 0 < s₀ < ℓ and δ := min(s₀, ℓ − s₀) > 0. For r > 0, blowUpMap x r sends φ(u) to r⁻¹(u − s₀)τ, so the image of I is contained in Q. Let f ∈ C_c(ℝ^P) and choose ρ > 0 with tsupport f ⊆ B̄_ρ(0). If 0 < r < δ/ρ and y = cτ ∈ Q has f(y) ≠ 0, then |c| = |y| ≤ ρ, so u := s₀ + rc satisfies |u − s₀| ≤ rρ < δ, hence u ∈ (0, ℓ) and y = blowUpMap x r (φ(u)) lies in the image of I. Thus f vanishes on Q ∖ blowUpMap x r '' I, and since Q is closed, ∫_{blowUpMap x r '' I} f dH¹ = ∫_Q f dH¹ for all r ∈ (0, δ/ρ) (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero). The integrals are therefore eventually constant in 𝓝[>] 0 and converge to ∫_Q f dH¹; with finrank Q = 1 this is HasApproximateTangentSpaceAt 1 I x Q.
6. The IMRep R := (I, 1, ζ₀) in ℝ^P of degree 1. I is Borel and I ⊆ ℝ^P. I is countably 1-rectifiable: it lies in the range of F(v) := a + v₀τ on EuclideanSpace ℝ (Fin 1), which is 1-Lipschitz (|v₀ − w₀| ≤ |v − w|, PiLp.norm_apply_le), since φ(u) = F(EuclideanSpace.single 0 u) (countablyRectifiable_range, CountablyRectifiable.mono). The multiplicity 1 is measurable and positive; ∫⁻_{I∩K} 1 dH¹ ≤ H¹(I) = ℓ < ∞; the constant orientation is a.e. strongly measurable; and for every x ∈ I (hence H¹⌞I-a.e., ae_restrict_iff') steps 4–5 give Q with HasApproximateTangentSpaceAt 1 I x Q and IsUnitOrientationOf ζ₀ Q.
7. By imrep_current there is S ∈ 𝒟_1(ℝ^P) represented by R, i.e. S(ω) = ∫_I ω(x)(τ) dH¹(x) for every ω ∈ 𝒟¹(ℝ^P). S is integer multiplicity.
8. Boundary. Let g be a test 0-form and ĝ(y) := g(y)⟨⟩. Then g(y) = constOfIsEmpty(ĝ(y)) (a 0-covector is determined by its value on the empty tuple), ĝ is C^∞ (composition of g with the continuous linear evaluation at ⟨⟩), and dg(y) = ofSubsingleton(Dĝ(y)) (extDeriv_constOfIsEmpty), so dg(y)(τ) = Dĝ(y)τ. By step 3, ∂S(g) = S(dg) = ∫_I Dĝ(x)τ dH¹ = ∫_{(0,ℓ)} Dĝ(a + uτ)τ du = ∫_0^ℓ Dĝ(a + uτ)τ du (integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le). By the chain rule u ↦ ĝ(a + uτ) has the continuous derivative Dĝ(a + uτ)τ, so the fundamental theorem of calculus (intervalIntegral.integral_eq_sub_of_hasDerivAt) gives ∂S(g) = ĝ(φ(ℓ)) − ĝ(φ(0)) = g(b)⟨⟩ − g(a)⟨⟩.
9. Mass. By (MR) with U = W = ℝ^P, M(S) = M_{ℝ^P}(S) = R.measure(ℝ^P) = ∫⁻_I 1 dH¹ = H¹(I) = ℓ < ∞.
10. Support. If ω ∈ 𝒟¹(ℝ^P) has tsupport disjoint from [a, b], then ω(x) = 0 for every x ∈ I ⊆ [a, b], so S(ω) = 0 (setIntegral_eq_zero_of_forall_eq_zero). [a, b] is compact (the continuous image of [0, 1], segment_eq_image), so support_vanish (U := ℝ^P, K := [a, b]) gives spt S ⊆ [a, b]. ∎

## Key steps

1. a = b: S = 0 (current_algebra (a), (b); support_vanish).
2. Isometric parametrization φ(u) = a + uτ of the open segment I; H¹⌞I is the image of Lebesgue measure on (0, ℓ).
3. (I, 1, α ↦ α(τ)) is an IMRep: rectifiable, of finite measure, and every point of I has approximate tangent line ℝτ because blow-ups of I eventually contain ℝτ ∩ spt f.
4. imrep_current gives the current S; ∂S(g) = ∫_0^ℓ (d/du) g(a + uτ)⟨⟩ du = g(b)⟨⟩ − g(a)⟨⟩.
5. M(S) = H¹(I) < ∞ by (MR); spt S ⊆ [a, b] by support_vanish.

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
