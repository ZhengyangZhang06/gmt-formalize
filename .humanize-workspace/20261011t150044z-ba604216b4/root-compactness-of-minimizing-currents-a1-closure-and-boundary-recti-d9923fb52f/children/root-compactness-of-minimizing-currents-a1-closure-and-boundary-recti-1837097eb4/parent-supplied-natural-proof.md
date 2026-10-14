# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.restriction_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Part (T2) steps 7-11 (one-sided smooth cut-off, error bound on the level band, limsup hypothesis on the compact band, continuity from above), with the integrability and cut-off details filled in. In Simon this convergence is the omitted step of Remark 8.3(1) to the closure theorem 8.2 (book/chapter-06.txt lines 2311-2316: “8.2(*) holds with T_{j'}⌞B_r(ξ) in place of T_j ...”, i.e. T_{j'}⌞{f<r} ⇀ T⌞{f<r} for f = |· − ξ| and a.e. r, justified there only by “an argument like that in 6.7(2) of Ch. 2”); the one-sided cut-off is the function γ_ε ∘ f (= 1 on {f ≤ t − ε}, = 0 on {f ≥ t}) of Simon's proof of Lemma 4.5(2) (lines 1262-1281), replaced here by a C^∞ function because X_j acts only on smooth test forms. Notation: |α|_E := covectorEuclideanNorm α for a k-covector α; for a fixed test form ω put g_j(x) := ξ_j(x)(ω(x)) and g(x) := ξ_X(x)(ω(x)).

1. Fix ω ∈ 𝒟^k(U) (TestFormOn U k: a C^∞ k-form on ℝ^P with compact support and tsupport ω ⊆ U) and let C := tsupport ω, a compact subset of U; hence μ_j(C), μ_X(C), μ(C) < ∞. The function x ↦ |ω(x)|_E is continuous (|·|_E is the square root of a finite sum of squares of the continuous linear evaluations α ↦ α(e_{I(1)}, …, e_{I(k)})) and vanishes off C (|0|_E = 0), so it is bounded (Continuous.bddAbove_range_of_hasCompactSupport); let M := sup_x |ω(x)|_E ∈ [0, ∞).

2. Integrability. By the admissibility hypothesis applied with α = ω(x): |g_j(x)| ≤ |ω(x)|_E ≤ M for μ_j-a.e. x, and |g(x)| ≤ M for μ_X-a.e. x. For x ∉ C, ω(x) = 0 and hence g_j(x) = g(x) = 0 by linearity of ξ_j(x), ξ_X(x). The functions g_j, g are a.e. strongly measurable (x ↦ (ξ_j(x), ω(x)) is a.e. strongly measurable and evaluation (L, α) ↦ L(α) is continuous). Hence g_j ∈ L¹(μ_j) and g ∈ L¹(μ_X) (bounded by M·1_C a.e., with μ_j(C), μ_X(C) < ∞), and so are their products with bounded measurable functions. Put a_j := ∫_{f<t} g_j dμ_j = ∫ 1_{f<t} g_j dμ_j and a := ∫_{f<t} g dμ_X ({f < t} is open since f is continuous, hence Borel).

3. Smooth one-sided cut-off. Let ε > 0. The sets C₁ := C ∩ {f ≤ t − ε} and C₂ := C ∩ {f ≥ t} are compact (closed subsets of C, f continuous), hence closed, and disjoint (f ≤ t − ε < t on C₁). Mathlib exists_contDiff_support_eq_eq_one_iff, applied with smoothness order n := ⊤ (so that ContDiff ℝ ↑n is ContDiff ℝ ∞, the order required by IsSmoothForm), the open set s := ℝ^P ∖ C₂ and the closed set C₁ ⊆ s, gives χ : ℝ^P → ℝ of class C^∞ with values in [0, 1], support χ = ℝ^P ∖ C₂ (so χ = 0 on C₂) and χ = 1 on C₁. (Unlike the parent proof, χ need not have compact support: χω inherits compact support from ω.)

4. The test form ω_ε := χω, i.e. x ↦ χ(x)·ω(x). It is C^∞ (ContDiff.smul), its support is contained in support ω, so it has compact support (HasCompactSupport.smul_left), and tsupport ω_ε ⊆ tsupport ω ⊆ U (tsupport_smul_subset_right); so ω_ε ∈ 𝒟^k(U). Since ξ_j(x), ξ_X(x) are linear, ξ_j(x)(ω_ε(x)) = χ(x) g_j(x) and ξ_X(x)(ω_ε(x)) = χ(x) g(x); by the representation hypotheses X_j(ω_ε) = ∫ χ g_j dμ_j and X(ω_ε) = ∫ χ g dμ_X.

5. Error estimate. For x ∈ C: if f(x) ≤ t − ε then x ∈ C₁ and 1_{f<t}(x) − χ(x) = 1 − 1 = 0; if f(x) ≥ t then x ∈ C₂ and 1_{f<t}(x) − χ(x) = 0 − 0 = 0; and always |1_{f<t}(x) − χ(x)| ≤ 1. Off C, g_j = g = 0. Hence, with B'_ε := C ∩ {t − ε < f < t} ⊆ B_ε := C ∩ {t − ε ≤ f ≤ t}, we have |(1_{f<t} − χ) g_j| ≤ M·1_{B'_ε} μ_j-a.e. and |(1_{f<t} − χ) g| ≤ M·1_{B'_ε} μ_X-a.e., so
|a_j − X_j(ω_ε)| = |∫ (1_{f<t} − χ) g_j dμ_j| ≤ M μ_j(B_ε) and |a − X(ω_ε)| ≤ M μ_X(B'_ε)
(all these measures are finite, being at most μ_j(C) resp. μ_X(C); the inequalities are between real numbers).

6. Shrinking the band. The Borel sets B_{1/n} (n ≥ 1) decrease with ⋂_n B_{1/n} = C ∩ {f = t}, and μ(B_1) ≤ μ(C) < ∞, so μ(B_{1/n}) → μ(C ∩ {f = t}) ≤ μ{f = t} = 0 (continuity from above, tendsto_measure_iInter_atTop). Likewise B'_{1/n} decreases to ∅ and μ_X(B'_1) < ∞, so μ_X(B'_{1/n}) → 0.

7. Convergence. Let η > 0 and η' := η/(3(M+1)) > 0. By step 6 choose n ≥ 1 with μ(B_{1/n}) < η' and μ_X(B'_{1/n}) < η', and let ε := 1/n. B_ε is a closed subset of C, hence a compact subset of U, so by hypothesis limsup_j μ_j(B_ε) ≤ μ(B_ε) < η', whence μ_j(B_ε) < η' for all large j (eventually_lt_of_limsup_lt). By weak convergence X_j(ω_ε) → X(ω_ε), so |X_j(ω_ε) − X(ω_ε)| < η/3 for all large j. For all such j, step 5 gives
|a_j − a| ≤ |a_j − X_j(ω_ε)| + |X_j(ω_ε) − X(ω_ε)| + |X(ω_ε) − a| < Mη' + η/3 + Mη' < η.
As η > 0 was arbitrary, a_j → a, i.e. ∫_{f<t} ξ_j(ω) dμ_j → ∫_{f<t} ξ_X(ω) dμ_X. ∎

## Key steps

1. C := tsupport ω is a compact subset of U and M := sup |ω|_E < ∞; the integrands are bounded by M·1_C a.e., so all integrals converge absolutely.
2. For ε > 0 a C^∞ χ : ℝ^P → [0,1] with χ = 1 on C ∩ {f ≤ t − ε} and χ = 0 on C ∩ {f ≥ t} (exists_contDiff_support_eq_eq_one_iff with n := ⊤) makes χω a test form in U with X_j(χω) = ∫ χ ξ_j(ω) dμ_j.
3. |a_j − X_j(χω)| ≤ M μ_j(C ∩ {t−ε ≤ f ≤ t}) and |a − X(χω)| ≤ M μ_X(C ∩ {t−ε < f < t}).
4. μ(C ∩ {t−1/n ≤ f ≤ t}) → μ(C ∩ {f = t}) = 0 and μ_X(C ∩ {t−1/n < f < t}) → 0; the limsup hypothesis on the compact band and X_j(χω) → X(χω) give a_j → a.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `grep -n '^def\|^structure\|^abbrev\|^theorem' SimonGMT Chapter06/Forms.lean Chapter06/Currents.lean; grep -rn covectorEuclideanNorm SimonGMT; sed Chapter06/Mass.lean and Chapter06/FormSupNorm.lean (IsTestForm = ContDiff ℝ ∞ ∧ HasCompactSupport; TestFormOn; WeaklyConvergesOn; covectorEuclideanNorm)`
- `grep -rn simon_theorem_4_16 SimonGMT (Chapter01/CompactMetrizableCompactness.lean simon_theorem_4_16_compact_metrizable; Chapter01/SequentialCompactnessCounterexample.lean simon_theorem_4_16_counterexample); grep -rn 'theorem .*limsup\|theorem .*liminf' SimonGMT (only WeaklyConvergesOn.massOn_le_liminf and Chapter08/VarifoldConvergence RadonConverges.*; no portmanteau or Radon compactness on open subsets of ℝ^P)`
- `grep -rn in snapshot mathlib/Mathlib: exists_contDiff_support_eq_eq_one_iff, exists_contDiff_tsupport_subset, 'def rieszMeasure', 'theorem integral_rieszMeasure', regular_rieszMeasure, exists_continuous_one_zero_of_isCompact, 'theorem Monotone.ae_differentiableAt', 'theorem measurable_deriv', 'theorem MonotoneOn.intervalIntegrable_deriv', 'theorem MonotoneOn.intervalIntegral_deriv_mem_uIcc', 'theorem lintegral_liminf_le', 'theorem measure_inter_add_sdiff', liminf_const_mul_of_ne_top, Monotone.map_liminf_of_continuousAt, extend_zero / continuous_extend_one / tsupport_extend_zero_subset, PositiveLinearMap.mk₀, apply_continuousLinearMap`
- `python3 scan of dag.json: 722 lean_names, none equal to cbr_vague_convergent_subseq, cbr_vague_limit_measure, cbr_vague_portmanteau, cbr_sublevel_restriction_tendsto, cbr_slice_mass_majorant; statements containing StrictMono/∫/limsup/liminf/rieszMeasure/deriv (found cmc_tendsto_integral_of_limsup_liminf [accepted, converse direction], cmc_rcc_ae_tendsto_measure_superlevel, dtc_bc_tendsto_integral_of_limsup_liminf, cmcs_smi_lintegral_ofReal_deriv_le [other branch, not accepted]); parent and sibling statuses and depends_on`
- `git grep of the five proposed names over all refs (GMT/*.lean) and grep -rl over the snapshot project and the SimonGMT package (no match); git show f9e4df7c999140c4c105810dbdfa2b7b37f1f1a3 (Submission.X declaration layout); survey of imports added to Submission.lean on other branches`
- `verifier/gmt-compare.py contract_scope and child_modules (challenge = import GMT.Ch07.Submission + replayed contract scope + theorem _root_.X : (stmt) := by exact Submission.name); verifier/lean_contract.py validate_lean_statement on the five statements (pass)`
- `lake env lean /tmp/cvt-decomp-x9f3/lean/Types.lean and Final.lean (each exact child string elaborates in the replayed scope; hypothesis-only assembly of the exact frozen parent type compiles; #print axioms: propext, Classical.choice, Quot.sound); Avail.lean..Avail4.lean (#check of every cited lemma; simon_theorem_4_16_compact_metrizable needs import Poincare.SimonGMT.Chapter01.CompactMetrizableCompactness, MonotoneOn.*deriv* need import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable); Avail5.lean (smooth cut-off via exists_contDiff_support_eq_eq_one_iff (n := ⊤), χ • ω is IsSmoothForm)`
- `awk/sed of book/chapter-01.txt lines 1522-1535 and 1740-1779 (Simon 1.4.12, 1.4.16); book/chapter-06.txt lines 1215-1300 (4.4-4.5), 1330-1400 (4.6-4.11), 2290-2420 (8.2-8.3); book/chapter-07.txt lines 245-300 (7.2.4 (13)-(14)); PROBLEM.md citation policy`
- `independent reviewer subagent over /tmp/cvt-decomp-x9f3/draft/subproblems.json and /tmp/cvt-decomp-x9f3/lean/Final.lean (verdict ACCEPT; non-blocking notes applied)`
- `WebSearch: Evans Gariepy weak convergence Radon measures limsup compact liminf open (Section 1.9)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/PROBLEM.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d9923fb52f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d9923fb52f/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/SequentialCompactnessCounterexample.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/cvt-decomp-x9f3/lean/Types.lean`
- `/tmp/cvt-decomp-x9f3/lean/Final.lean`
- `/tmp/cvt-decomp-x9f3/lean/Avail5.lean`
- `/tmp/cvt-decomp-x9f3/draft/subproblems.json`

The snapshot contract is identical to the workspace Contract.lean and Submission.lean. The DAG and branches contain no accepted declaration that proves T1, T2 or MM. The closest are cmc_tendsto_integral_of_limsup_liminf (accepted), which is the converse of the portmanteau, and cmcs_smi_lintegral_ofReal_deriv_le, a monotone-derivative bound in another branch that is not accepted. SimonGMT has only the compact-metrizable form of Simon 4.16, which applies on compact pieces, and no Radon-measure portmanteau. Every Mathlib/SimonGMT lemma cited in the child proofs exists: RMK (RealRMK.rieszMeasure, integral_rieszMeasure, regular_rieszMeasure), extend-by-zero support lemmas, exists_contDiff_support_eq_eq_one_iff, Monotone.ae_differentiableAt, measurable_deriv, MonotoneOn.intervalIntegral_deriv_mem_uIcc, lintegral_liminf_le, ENNReal.liminf_const_mul_of_ne_top, tendsto_measure_cthickening and others. Exactly two need an added import, both verified to load with GMT.Ch07.Submission. The five proposed exact statements elaborate in the replayed contract scope and pass the verifier's lexical check; their names are unused. A hypothesis-only assembly proves the exact frozen parent type from them with axioms propext, Classical.choice and Quot.sound only. Book anchors: Simon 1.4.16 (chapter-01 lines 1750-1778), 1.4.12 (1522-1527), 6.4.5(2) cut-off (chapter-06 lines 1262-1281), 6.4.9-4.10 (1356-1377), 6.8.2-8.3 (2303-2347), 7.2.4 (13)-(14) (chapter-07 lines 264-288).
