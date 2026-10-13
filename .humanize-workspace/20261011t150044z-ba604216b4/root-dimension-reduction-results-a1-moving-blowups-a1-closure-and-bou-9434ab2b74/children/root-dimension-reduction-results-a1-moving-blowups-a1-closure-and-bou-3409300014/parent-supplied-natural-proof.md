# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.restriction_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Part (T2), steps 7-11 (smooth one-sided cut-off, error bound on the level band, limsup hypothesis on the compact band, continuity from above), with the integrability and cut-off details filled in. One simplification of step 8, said explicitly: the cut-off χ_ε is taken one-sided on all of ℝ^P (χ_ε = 1 on {f ≤ t − ε}, χ_ε = 0 on {f ≥ t}). It need not have compact support, because χ_εω inherits compact support from ω. In particular χ_ε = 1 on C₁ = C ∩ {f ≤ t − ε} and χ_ε = 0 on C₂ = C ∩ {f ≥ t}, which is all that steps 9-11 use. Notation: |α|_E := covectorEuclideanNorm α for a k-covector α. For the fixed test form ω put g_j(x) := ξ_j(x)(ω(x)) and g(x) := ξ_X(x)(ω(x)). Every tool below is in the frozen import closure: exists_contDiff_support_eq_eq_one_iff, tendsto_measure_iInter_atTop and eventually_lt_of_limsup_lt.

1. (parent step 7) Fix ω ∈ 𝒟^k(U), i.e. a TestFormOn U k: a C^∞ k-form on ℝ^P with compact support and tsupport ω ⊆ U. C := tsupport ω is a compact subset of U, so μ_j(C), μ_X(C), μ(C) < ∞ by hypothesis. The function x ↦ |ω(x)|_E is continuous: ω is continuous, and |·|_E is the square root of a finite sum of squares of the continuous linear evaluations α ↦ α(e_{I(1)}, …, e_{I(k)}). It vanishes off C (|0|_E = 0), so it is bounded (continuous with compact support). Let M := sup_x |ω(x)|_E ∈ [0, ∞) (this is ‖ω‖_∞ of the parent).

2. Integrability. By the admissibility hypothesis applied with α = ω(x), |g_j(x)| ≤ |ω(x)|_E ≤ M for μ_j-a.e. x, and |g(x)| ≤ M for μ_X-a.e. x. For x ∉ C, ω(x) = 0, hence g_j(x) = g(x) = 0 by linearity of ξ_j(x) and ξ_X(x). The functions g_j and g are a.e. strongly measurable: x ↦ (ξ_j(x), ω(x)) is a.e. strongly measurable, and evaluation (L, α) ↦ L(α) is continuous. Hence g_j ∈ L¹(μ_j) and g ∈ L¹(μ_X), since they are bounded by M·1_C a.e. and μ_j(C), μ_X(C) < ∞; so are their products with bounded Borel functions. The set {f < t} is open (f continuous), hence Borel. Put a_j := ∫_{f<t} g_j dμ_j = ∫ 1_{f<t} g_j dμ_j and a := ∫_{f<t} g dμ_X.

3. Smooth one-sided cut-off (parent step 8). Let ε > 0. The set s := {f < t} is open, the set c := {f ≤ t − ε} is closed, and c ⊆ s. Mathlib exists_contDiff_support_eq_eq_one_iff, applied with smoothness order n := ⊤ (so that ContDiff ℝ ↑n is ContDiff ℝ ∞, the order required by IsSmoothForm), gives a C^∞ function χ : ℝ^P → ℝ with values in [0, 1], support χ = s, and χ(x) = 1 exactly when x ∈ c (in particular χ = 1 on c). Thus χ(x) = 1 whenever f(x) ≤ t − ε, and χ(x) = 0 whenever f(x) ≥ t.

4. The test form ω_ε := χω, i.e. x ↦ χ(x)·ω(x). It is C^∞ (ContDiff.smul). Its support is contained in support ω, so it has compact support (HasCompactSupport.smul_left), and tsupport ω_ε ⊆ tsupport ω ⊆ U (tsupport_smul_subset_right). So ω_ε ∈ 𝒟^k(U). Since ξ_j(x) and ξ_X(x) are linear, ξ_j(x)(ω_ε(x)) = χ(x) g_j(x) and ξ_X(x)(ω_ε(x)) = χ(x) g(x). By the representation hypotheses, X_j(ω_ε) = ∫ χ g_j dμ_j and X(ω_ε) = ∫ χ g dμ_X.

5. Error estimate (parent step 9). For every x: if f(x) ≤ t − ε then 1_{f<t}(x) − χ(x) = 1 − 1 = 0; if f(x) ≥ t then 1_{f<t}(x) − χ(x) = 0 − 0 = 0; and always |1_{f<t}(x) − χ(x)| ≤ 1. Off C, g_j = g = 0.
Put B'_ε := C ∩ {t − ε < f < t} ⊆ B_ε := C ∩ {t − ε ≤ f ≤ t}. Then |(1_{f<t} − χ) g_j| ≤ M·1_{B'_ε} μ_j-a.e., and |(1_{f<t} − χ) g| ≤ M·1_{B'_ε} μ_X-a.e. Since a_j − X_j(ω_ε) = ∫ (1_{f<t} − χ) g_j dμ_j, we get
|a_j − X_j(ω_ε)| ≤ M μ_j(B'_ε) ≤ M μ_j(B_ε) and |a − X(ω_ε)| ≤ M μ_X(B'_ε).
These are inequalities between real numbers: all the measures involved are at most μ_j(C) resp. μ_X(C) < ∞.

6. Shrinking the band (parent step 11). The Borel sets B_{1/n} (n ≥ 1) decrease, with ⋂_n B_{1/n} = C ∩ {f = t}, and μ(B_1) ≤ μ(C) < ∞. So μ(B_{1/n}) → μ(C ∩ {f = t}) ≤ μ{f = t} = 0 (continuity from above, tendsto_measure_iInter_atTop). Likewise B'_{1/n} decreases to ∅ and μ_X(B'_1) < ∞, so μ_X(B'_{1/n}) → 0.

7. Convergence (parent steps 10-11). Let e > 0 and δ := e/(3(M+1)) > 0. By step 6 choose n ≥ 1 with μ(B_{1/n}) < δ and μ_X(B'_{1/n}) < δ. Let ε := 1/n and take χ and ω_ε from steps 3-4.
B_ε is closed (f continuous) and contained in the compact set C ⊆ U, so it is a compact subset of U. By hypothesis limsup_j μ_j(B_ε) ≤ μ(B_ε) < δ, so μ_j(B_ε) < δ for all large j (eventually_lt_of_limsup_lt).
By weak convergence (WeaklyConvergesOn: X_j(ω') → X(ω') for every ω' ∈ 𝒟^k(U)), X_j(ω_ε) → X(ω_ε), so |X_j(ω_ε) − X(ω_ε)| < e/3 for all large j.
For all such j, step 5 gives
|a_j − a| ≤ |a_j − X_j(ω_ε)| + |X_j(ω_ε) − X(ω_ε)| + |X(ω_ε) − a| < Mδ + e/3 + Mδ < e.
As e > 0 was arbitrary, a_j → a, i.e. ∫_{f<t} ξ_j(ω) dμ_j → ∫_{f<t} ξ_X(ω) dμ_X. (The hypothesis that U is open is not used.) ∎

## Key steps

1. C := tsupport ω is a compact subset of U and M := sup |ω|_E < ∞; the integrands ξ(ω) are bounded by M·1_C a.e., so all integrals converge absolutely.
2. For ε > 0, exists_contDiff_support_eq_eq_one_iff (n := ⊤) gives a C^∞ χ : ℝ^P → [0,1] with χ = 1 on {f ≤ t − ε} and χ = 0 on {f ≥ t}; then χω ∈ 𝒟^k(U) and X_j(χω) = ∫ χ ξ_j(ω) dμ_j.
3. |a_j − X_j(χω)| ≤ M μ_j(C ∩ {t−ε ≤ f ≤ t}) and |a − X(χω)| ≤ M μ_X(C ∩ {t−ε < f < t}).
4. μ(C ∩ {t−1/n ≤ f ≤ t}) → μ(C ∩ {f = t}) = 0 and μ_X(C ∩ {t−1/n < f < t}) → 0; the limsup hypothesis on the compact band and X_j(χω) → X(χω) give a_j → a.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -c 'dmcbr_|cbr_vague|cbr_sublevel|cbr_slice' SNAPSHOT (no match)`
- `rg -n over SNAPSHOT/mathlib/Mathlib, all found: exists_contDiff_support_eq_eq_one_iff, RealRMK rieszMeasure / integral_rieszMeasure, IsOpen.locallyCompactSpace, tendsto_measure_cthickening(_of_isClosed), IsCompact.exists_cthickening_subset_open, Monotone.ae_differentiableAt, measurable_deriv, lintegral_liminf_le, measure_inter_add_sdiff, ENNReal liminf_const_mul_of_ne_top, tendsto_measure_iInter_atTop, tendsto_measure_iUnion_atTop, exists_continuous_one_zero_of_isCompact, integral_subtype_comap, setIntegral_eq_integral_of_forall_compl_eq_zero, StrictMono.id_le, strictMono_nat_of_lt_succ, eventually_lt_of_limsup_lt (to_dual), ofReal_integral_eq_lintegral_ofReal, Monotone.deriv_nonneg, hasDerivAt_iff_tendsto_slope, MeasurableEmbedding.subtype_coe, tendsto_add_atTop_iff_nat, ae_all_iff, Measurable.liminf, continuous_extend_one / extend_one / mulTSupport_extend_one_subset (to_additive sources of the extend_zero lemmas), MonotoneOn.intervalIntegrable_deriv and MonotoneOn.intervalIntegral_deriv_mem_uIcc (in IntervalIntegral/DerivIntegrable.lean)`
- `rg -n 'theorem simon_theorem_4_16_compact_metrizable' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean; rg -n 'def covectorEuclideanNorm|def WeaklyConvergesOn|abbrev TestFormOn|def IsTestForm|def IsSmoothForm|abbrev Covector|abbrev DifferentialForm' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06`
- `lake env lean (v4.35.0-rc3): /tmp/dmcbr_ct_split/Types.lean (5 sorry warnings only), Assembly.lean (axioms propext, Classical.choice, Quot.sound), Avail.lean (simon_theorem_4_16_compact_metrizable, MonotoneOn.intervalIntegrable_deriv, MonotoneOn.intervalIntegral_deriv_mem_uIcc unknown under the frozen imports; everything else used available), Sigs.lean (#check of Monotone.ae_hasDerivAt, StieltjesFunction.measure_Ioo, Measure.withDensity_rnDeriv_le, ENNReal.liminf_const_mul_of_ne_top, lintegral_liminf_le, RealRMK.rieszMeasure, exists_contDiff_support_eq_eq_one_iff, IsCompact.tendsto_subseq, TopologicalSpace.denseSeq, eventually_lt_of_limsup_lt, HasCompactSupport.continuous_extend_zero, tendsto_measure_cthickening_of_isClosed, Monotone.le_rightLim, Monotone.rightLim_le)`
- `verifier lean_contract.validate_lean_statement on all five child types (OK)`
- `python scans of RUN/dag.json: twin node cbr_measure_convergence_tools with byte-identical type; statuses and candidate commits of its subtree (re-read just before submission); byte-identity of reused types; absence of the three fresh names`
- `git log --all -S<each fresh name> (no hits); git log --all -G'^import (CompactMetrizableCompactness|DerivIntegrable)' -- GMT/Ch07/Submission.lean (9a4fdc59b added, fa0865963 removed); git show 7920d7e, ef83328, fa0865963, b8056c4, 9e4623f, 92ece76`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint' /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-9434ab2b74/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d9923fb52f/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b85187fcb1/decomposition-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/dmcbr_ct_split/Types.lean`
- `/tmp/dmcbr_ct_split/Assembly.lean`
- `/tmp/dmcbr_ct_split/Avail.lean`
- `/tmp/dmcbr_ct_split/Sigs.lean`

Pins match: the snapshot is project b4d606d (= HEAD) with Mathlib 25730c7c, and Submission.lean equals the frozen contract.

Names: the snapshot contains no dmcbr_ or cbr_ declarations. The three fresh child names are unused in the DAG, in git history and in the run directory.

Cited lemmas: every Mathlib and SimonGMT name cited by the child proofs exists in the pinned sources. simon_theorem_4_16_compact_metrizable (SimonGMT Chapter01), MonotoneOn.intervalIntegrable_deriv and MonotoneOn.intervalIntegral_deriv_mem_uIcc (IntervalIntegral/DerivIntegrable.lean) are outside the frozen import closure. The child proofs therefore replace them with import-free arguments: the direct Claim A, and the Stieltjes/rnDeriv form of Lebesgue's inequality. Every lemma those arguments use was #checked under `import GMT.Ch07.Submission`.

Reuse: the twin node cbr_measure_convergence_tools has this node's exact type. Its children cbr_vague_limit_measure and cbr_vague_portmanteau are accepted with byte-identical types and are reused.

Lean checks: all five child types elaborate, and the sorry-free hypothesis assembly proves the exact parent type with axioms propext, Classical.choice, Quot.sound.
