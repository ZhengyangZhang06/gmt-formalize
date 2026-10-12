# Parent-supplied natural-language proof

- Parent DAG node: `root.bv_results-a1.extension-a1`
- Child DAG node: `root.bv_results-a1.extension-a1.weighted_gradient-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof of Simon 2.8, Section C4 (Simon's (5): δ∫|Dφ||u| ≤ −∫x·Dφ|u| = ∫|u| div(xφ) … ≤ ∫_U|D|u|| + n∫|u|), with a general r in place of δR and with |D|u||(U) kept (the caller replaces it by |Du|(U)).
Notation: E := Rn n, μ := volume, Dφ := fderiv ℝ φ, K a Lipschitz constant of φ, A := ∫⁻ x in U, ‖u x‖ₑ, M' := bvVariationOn (fun x ↦ |u x|) U.
1. If r ≤ 0 then ofReal r = 0 and the left side is 0. Assume r > 0.
2. The field V. Put c(y) := R⁻¹•(y − ξ) and V(y) := φ(y)•c(y). (i) If φ(y) ≠ 0 then y ∈ tsupport φ ⊆ U ⊆ closedBall ξ R, so ‖y − ξ‖ ≤ R. (ii) V is (K + R⁻¹)-Lipschitz (LipschitzWith.of_dist_le_mul): if φ(x) ≠ 0 then V(x) − V(y) = R⁻¹•((φ(x) − φ(y))•(x − ξ) + φ(y)•(x − y)), so ‖V(x) − V(y)‖ ≤ R⁻¹(K‖x − y‖·R + 1·‖x − y‖) by (i) and |φ(y)| ≤ 1; the case φ(y) ≠ 0 is symmetric; if φ(x) = φ(y) = 0 then V(x) = V(y) = 0. (iii) support V ⊆ support φ, so tsupport V ⊆ tsupport φ ⊆ U and V has compact support (HasCompactSupport.smul_right). (iv) ‖V(y)‖ = φ(y)‖y − ξ‖/R ≤ 1 by (i).
3. Admissibility of −V. The field −V (fun y ↦ −V y) is (K + R⁻¹)-Lipschitz, has compact support (HasCompactSupport.neg), tsupport (−V) = tsupport V ⊆ U (tsupport_neg) and ‖−V(y)‖ ≤ 1. By Submission.bv_ext_ofReal_integral_le_bvVariationOn (v := fun x ↦ |u x|, G := −V, W := U): ofReal(b) ≤ M', where b := ∫ x in U, |u x| · div(−V)(x).
4. div(−V) = −div V at every point, because fderiv ℝ (fun y ↦ −V y) x = −fderiv ℝ V x for all x (fderiv_fun_neg) and the trace is linear. Also div(−V) vanishes off tsupport(−V) ⊆ U (Chapter02.support_euclideanDivergence_subset), so b = ∫ |u|·div(−V) = −∫ |u|·div V (setIntegral_eq_integral_of_forall_compl_eq_zero, integral_neg).
5. Divergence of V. c is differentiable everywhere with fderiv ℝ c x = R⁻¹•id, whose trace is R⁻¹·finrank ℝ E = R⁻¹·n (LinearMap.trace_id, finrank_euclideanSpace_fin); so div c ≡ n/R. φ is Lipschitz, hence differentiable at μ-a.e. x (LipschitzWith.ae_differentiableAt). At such x, Submission.bv_ext_euclideanDivergence_smul (with g := c) gives div V(x) = φ(x)·n/R + Dφ(x)[R⁻¹•(x − ξ)] = (n·φ(x) + Dφ(x)[x − ξ])/R, i.e. −Dφ(x)[x − ξ] = n·φ(x) − R·div V(x).
6. Pointwise a.e. inequality. Combining step 5 with the a.e. hypothesis r‖Dφ(x)‖ ≤ −Dφ(x)[x − ξ] and multiplying by |u(x)| ≥ 0: for μ-a.e. x, r·|u(x)|·‖Dφ(x)‖ ≤ n·|u(x)|·φ(x) − R·|u(x)|·div V(x).
7. Integrability. u ∈ L¹. ‖Dφ(x)‖ ≤ K for all x (norm_fderiv_le_of_lipschitz) and x ↦ ‖Dφ(x)‖ is measurable (measurable_fderiv); φ is continuous with 0 ≤ φ ≤ 1; |div V| ≤ n(K + R⁻¹) (Chapter02.norm_euclideanDivergence_le_of_lipschitz) and div V is measurable (Chapter02.measurable_euclideanDivergence). Hence |u|·‖Dφ‖, |u|·φ and |u|·div V are integrable (integrable times bounded measurable).
8. Integrating step 6 (integral_mono_ae, integral_sub, integral_const_mul): r·∫|u|‖Dφ‖ ≤ n·∫|u|φ − R·∫|u|·div V.
9. First term: |u|φ vanishes off U and |u|φ ≤ |u|, so ∫|u|φ = ∫ x in U, |u|φ ≤ ∫ x in U, |u| =: a (setIntegral_eq_integral_of_forall_compl_eq_zero, then setIntegral_mono_on, U being measurable because it is open), and ofReal a = A (ofReal_integral_norm_eq_lintegral_enorm; u is integrable on U).
10. Second term: −∫|u|·div V = b by step 4, and ofReal b ≤ M' by step 3.
11. Conclusion. r·∫|u|‖Dφ‖ ≤ n·a + R·b. The integrand |u|‖Dφ‖ is nonnegative and integrable and ‖u x‖ₑ·‖Dφ x‖ₑ = ofReal(|u x|·‖Dφ x‖), so ∫⁻ ‖u‖ₑ‖Dφ‖ₑ = ofReal(∫|u|‖Dφ‖) (ofReal_integral_eq_lintegral_ofReal) and ofReal r · ∫⁻ ‖u‖ₑ‖Dφ‖ₑ = ofReal(r·∫|u|‖Dφ‖) (ENNReal.ofReal_mul, r ≥ 0). Finally, by ENNReal.ofReal_le_ofReal, ENNReal.ofReal_add_le and ENNReal.ofReal_mul (n, R ≥ 0): ofReal(n·a + R·b) ≤ n·ofReal a + ofReal R·ofReal b ≤ n·A + ofReal R·M' = ofReal R·M' + n·A. (If M' = ∞ the claim is trivial since R > 0.) ∎

## Key steps

1. Trivial if r ≤ 0; otherwise build V = φ·(x − ξ)/R: Lipschitz, compact support in U, ‖V‖ ≤ 1 (uses U ⊆ closedBall ξ R).
2. −V is admissible for U, so ofReal(∫_U |u| div(−V)) ≤ |D|u||(U) (Submission.bv_ext_ofReal_integral_le_bvVariationOn); div(−V) = −div V vanishes off U.
3. A.e. (Rademacher + Submission.bv_ext_euclideanDivergence_smul): R div V = nφ + Dφ[x − ξ], so r|u|‖Dφ‖ ≤ n|u|φ − R|u| div V a.e.
4. Integrate: r∫|u|‖Dφ‖ ≤ n∫_U|u| + R∫_U|u| div(−V), then convert to [0,∞] with ofReal_add_le and ofReal_mul.

## Reference use

### local-project

Queries:
- `rg -n 'addHaar_frontier' mathlib/Mathlib/Analysis/Convex/`
- `rg -n 'countable_meas_pos_of_disjoint' mathlib/Mathlib/MeasureTheory/Measure/ ; sed -n 245,330p mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean (countable_meas_level_set_pos)`
- `rg -n 'exists_infDist_eq_dist|lipschitz_infDist_pt|theorem infDist_pos|notMem_iff_infDist_pos|theorem le_infDist|infDist_le_dist_of_mem|infDist_eq_zero_of_mem|theorem infDist_empty' mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `rg -n 'infDist|infEDist' mathlib/Mathlib/Analysis/Convex/ (no match)`
- `rg -n '^theorem|^lemma' mathlib/Mathlib/Analysis/Convex/Deriv.lean (ConvexOn/ConcaveOn slope-derivative lemmas)`
- `rg -n 'trace_smulRight|trace_id|trace_one|trace_eq_contract' mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `rg -n 'fderiv_smul|HasFDerivAt.smul' mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean ; rg -n 'ae_differentiableAt' mathlib/Mathlib/Analysis/Calculus/Rademacher.lean ; rg -n 'norm_fderiv_le_of_lipschitz' mathlib/Mathlib/Analysis/Calculus/FDeriv/`
- `rg -n -A3 'setIntegral_eq_integral_of_forall_compl_eq_zero|setLIntegral_eq_of_support_subset|countable_meas_level_set_pos' mathlib/Mathlib/MeasureTheory/`
- `rg -n 'dense_compl' mathlib/Mathlib/Topology/ mathlib/Mathlib/Analysis/ ; rg -n 'Countable.measure_zero' mathlib/Mathlib/MeasureTheory/`
- `full read of simongmt Poincare/SimonGMT/Chapter02/BV.lean; read GMT/Ch02/Contract.lean and README rows for 2.8; cmp snapshot project/GMT/Ch02/Contract.lean with the workspace Contract.lean; sed -n 655,745p book/sources/chapter-02-source.txt`
- `lean Avail.lean, Avail2.lean, Avail3.lean, Avail4.lean: #check of every cited lemma after import GMT.Ch02.Submission`
- `python3 -I gen_checks.py (verifier gmt-compare.py layout/child_modules/contract_scope plus lean_contract.validate_lean_statement), then lean NodeChallenge_00..08.lean and Print.lean`
- `lean Assembly.lean with #print axioms GMT.Ch02.node_check; lean Small.lean; lean Integrated.lean with #print axioms of the 9 children`
- `grep -rl for each of the 9 proposed lean_names in the run directory; lean_name of every dag.json node and nodes/*/decomposition-v*.json subproblem`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Convex/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Convex/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Algebra/Module/Cardinality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-extension-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1/decomposition-v1.json`
- `/tmp/extdecomp-ilC422/checks/NodeChallenge_00.lean`
- `/tmp/extdecomp-ilC422/checks/NodeChallenge_08.lean`
- `/tmp/extdecomp-ilC422/checks/Assembly.lean`
- `/tmp/extdecomp-ilC422/checks/Small.lean`
- `/tmp/extdecomp-ilC422/checks/Avail.lean`
- `/tmp/extdecomp-ilC422/verify/Integrated.lean`

The snapshot project/GMT/Ch02/Contract.lean is byte-identical to the workspace contract (cmp). Rn, IsBVOn and BVExtensionEstimate match the selected type. README row 9 and its judgment-call note match the readings used: u = 0 a.e. off Ū, and |Du|(ℝⁿ∖Ū) = 0. The pinned SimonGMT BV.lean supplies every SimonGMT name the children use: euclideanDivergence, bvVariationOn, IsLipschitzTestField, compactlySupportedSupNorm, ofReal_integral_le_bvVariationOn, support_euclideanDivergence_subset, measurable_euclideanDivergence and norm_euclideanDivergence_le_of_lipschitz. The snapshot Mathlib supplies the cited tools: Metric.le_infDist, infDist_le_dist_of_mem, lipschitz_infDist_pt, IsClosed.exists_infDist_eq_dist, IsClosed.notMem_iff_infDist_pos, ConcaveOn.slope_le_of_hasDerivAt, HasDerivAt.tendsto_slope_zero_right, LipschitzWith.ae_differentiableAt, norm_fderiv_le_of_lipschitz, fderiv_fun_smul, LinearMap.trace_smulRight, LinearMap.trace_id, Measure.countable_meas_level_set_pos, Set.Countable.measure_zero, setIntegral_eq_integral_of_forall_compl_eq_zero and Convex.addHaar_frontier. After import GMT.Ch02.Submission all of these are available except two: Convex.addHaar_frontier (Mathlib.Analysis.Convex.Measure, needed only by the parent assembly) and the optional alternative Set.Countable.dense_compl (Mathlib.Topology.Algebra.Module.Cardinality). Adding Submission imports is allowed, because the verifier freezes only Contract.lean and the Lake inputs. Two searches found nothing. No Mathlib lemma states concavity of the distance to the complement of a convex set (no infDist match under Analysis/Convex). Neither Mathlib nor SimonGMT has a BV extension estimate. These are therefore genuine new obligations. All 9 child statements elaborate in the comparator's replayed scope. Each has a complete Lean proof using only standard axioms, and the Lean assembly proves the selected type from them plus Submission.bv_abs_variation_le.
