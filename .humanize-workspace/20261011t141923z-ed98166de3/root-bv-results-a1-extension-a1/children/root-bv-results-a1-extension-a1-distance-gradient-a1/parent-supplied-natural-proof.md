# Parent-supplied natural-language proof

- Parent DAG node: `root.bv_results-a1.extension-a1`
- Child DAG node: `root.bv_results-a1.extension-a1.distance_gradient-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof of Simon 2.8, Section C1(c) ('|Dd(x)| = 1 at points of differentiability in U'), with S in place of Uᶜ.
Notation: E := Rn n (finite-dimensional, hence a proper metric space), d(y) := infDist y S, L := fderiv ℝ d x.
1. Upper bound. d is 1-Lipschitz (Metric.lipschitz_infDist_pt), so ‖L‖ ≤ 1 (norm_fderiv_le_of_lipschitz).
2. Nearest point. S is closed and nonempty and E is proper, so there is a ∈ S with d(x) = dist x a (IsClosed.exists_infDist_eq_dist). As x ∉ S and S is closed, ρ := d(x) > 0 (IsClosed.notMem_iff_infDist_pos); hence ‖a − x‖ = ρ > 0.
3. Put e := ρ⁻¹•(a − x), so ‖e‖ = 1. For 0 ≤ t ≤ ρ we have a − (x + t•e) = (1 − t/ρ)•(a − x) with 1 − t/ρ ≥ 0, so dist(x + t•e, a) = (1 − t/ρ)·ρ = ρ − t and therefore d(x + t•e) ≤ dist(x + t•e, a) = d(x) − t (Metric.infDist_le_dist_of_mem).
4. Directional derivative. Let h(t) := d(x + t•e). The map t ↦ x + t•e has derivative e and value x at t = 0, and d is differentiable at x, so HasDerivAt h (L e) 0 (HasFDerivAt.comp_hasDerivAt). Consequently the one-sided difference quotients t⁻¹·(h(t) − h(0)) tend to L e as t → 0 with t > 0 (HasDerivAt.tendsto_slope_zero_right). For 0 < t ≤ ρ step 3 gives (h(t) − h(0))/t ≤ −1, and such t form a neighbourhood of 0 within Ioi 0, so L e ≤ −1 (le_of_tendsto).
5. Lower bound. 1 ≤ −L e ≤ |L e| = ‖L e‖ ≤ ‖L‖·‖e‖ = ‖L‖ (ContinuousLinearMap.le_opNorm).
6. Steps 1 and 5 give ‖L‖ = 1. (When n = 0 the hypotheses are contradictory: E has one point, so the nonempty S is all of E and x ∉ S is impossible; the argument above does not need this remark.) ∎

## Key steps

1. ‖Dd(x)‖ ≤ 1 because d = infDist(·,S) is 1-Lipschitz.
2. Pick a nearest point a ∈ S (proper space, S closed nonempty); ρ = d(x) = ‖a − x‖ > 0.
3. Along e = (a − x)/ρ, d(x + te) ≤ d(x) − t for 0 ≤ t ≤ ρ, so the one-sided difference quotients give Dd(x)[e] ≤ −1.
4. Hence ‖Dd(x)‖ ≥ |Dd(x)[e]| ≥ 1, and ‖Dd(x)‖ = 1.

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
