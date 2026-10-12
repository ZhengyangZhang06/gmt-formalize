# Parent-supplied natural-language proof

- Parent DAG node: `root.density_semicontinuity-a1.weight_portmanteau-a1`
- Child DAG node: `root.density_semicontinuity-a1.weight_portmanteau-a1.urysohn_sandwich-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 3 (Urysohn functions) and Step 2 (lintegral form) of the parent proof, combined into one test function that works for every admissible measure.

Let K ⊆ ℝ^N be compact and O ⊆ ℝ^N open with K ⊆ O. Recall that ℝ^N = Euclidean N is locally compact and Hausdorff, hence regular.

1. By exists_compact_between there is a compact L with K ⊆ interior L and L ⊆ O.

2. K is compact, (interior L)ᶜ is closed, and they are disjoint because K ⊆ interior L. Urysohn's lemma in a regular locally compact space (exists_continuous_one_zero_of_isCompact) gives a continuous f : ℝ^N → ℝ such that:
 - f = 1 on K;
 - f = 0 on (interior L)ᶜ;
 - f has compact support;
 - 0 ≤ f(x) ≤ 1 for all x.
 Let g := f.

3. tsupport g ⊆ L ⊆ O. If g(x) ≠ 0, then x ∉ (interior L)ᶜ, so x ∈ interior L ⊆ L. Thus support g ⊆ L. L is closed (compact in a Hausdorff space), so tsupport g = closure(support g) ⊆ L (closure_minimal). Hence g is continuous, has compact support, and tsupport g ⊆ O: these are the first three conclusions. The function g is now fixed and does not depend on any measure.

4. Let ν be a measure on ℝ^N with ν(L') ≠ ∞ for every compact L' ⊆ O. In particular ν(L) < ∞, since L is compact and L ⊆ O.

5. g is ν-integrable. g is continuous, hence AE-strongly measurable; |g(x)| ≤ 1 for all x; and ν(L) < ∞. So g is integrable on L (Measure.integrableOn_of_bounded with bound 1). Since support g ⊆ tsupport g ⊆ L, integrability on L is equivalent to integrability on ℝ^N (integrableOn_iff_integrable_of_support_subset).

6. g ≥ 0 everywhere and g is integrable, so ENNReal.ofReal(∫ g dν) = ∫⁻ ENNReal.ofReal(g(x)) dν(x) (ofReal_integral_eq_lintegral_ofReal).

7. Pointwise comparison, for every x:
 - 1_K(x) ≤ ofReal(g(x)). If x ∈ K, then g(x) = 1 and ofReal(1) = 1. If x ∉ K, the left side is 0.
 - ofReal(g(x)) ≤ 1_O(x). If x ∈ O, then ofReal(g(x)) ≤ 1 because g(x) ≤ 1 (ENNReal.ofReal_le_one). If x ∉ O, then x ∉ tsupport g (as tsupport g ⊆ O), so g(x) = 0 (image_eq_zero_of_notMem_tsupport) and ofReal(g(x)) = 0.

8. K is closed and O is open, so both are measurable, and ∫⁻ 1_K dν = ν(K), ∫⁻ 1_O dν = ν(O) (lintegral_indicator_one). Monotonicity of the lower integral (lintegral_mono) and step 7 give ν(K) ≤ ∫⁻ ofReal ∘ g dν ≤ ν(O). By step 6 the middle term equals ENNReal.ofReal(∫ g dν). Hence ν(K) ≤ ofReal(∫ g dν) ≤ ν(O) for every ν as in step 4, with the single g from steps 2–3. ∎

## Key steps

1. Choose a compact L with K ⊆ interior L and L ⊆ O (exists_compact_between).
2. Urysohn: continuous, compactly supported g with values in [0,1], g = 1 on K and g = 0 off interior L; hence tsupport g ⊆ L ⊆ O.
3. For ν finite on compacts in O: ν(L) < ∞ and g is bounded with support in L, so g is ν-integrable and ofReal(∫ g dν) = ∫⁻ ofReal ∘ g dν.
4. Pointwise 1_K ≤ ofReal ∘ g ≤ 1_O; integrate to get ν(K) ≤ ofReal(∫ g dν) ≤ ν(O).

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `grep -n 'RadonConverges\|def weight\|domainMeasure\|weight_finite_on_compact\|isOpen_domain\|structure Varifold\|map_domainMeasure' simongmt Poincare/SimonGMT/Chapter08/Varifold.lean; cat Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `rg -n 'theorem exists_continuous_one_zero_of_isCompact|theorem exists_compact_between|theorem exists_continuous_nonneg_pos' mathlib/Mathlib`
- `rg -n 'exists_iUnion_isClosed|theorem Monotone.measure_iUnion|theorem tendsto_measure_iInter_atTop|theorem IsCompact.exists_cthickening_subset_open|theorem closure_eq_iInter_thickening|theorem ofReal_integral_eq_lintegral_ofReal|IsCompact.cthickening|theorem self_subset_thickening|theorem thickening_subset_cthickening|theorem thickening_mono' mathlib/Mathlib`
- `rg -n 'theorem le_liminf_measure_open|theorem limsup_measure_closed_le|le_liminf_measure|limsup_measure.*_le' mathlib/Mathlib; rg -il vague mathlib/Mathlib (no match)`
- `rg -n 'lintegral_indicator_one|integrableOn_iff_integrable_of_support_subset|lemma Measure.integrableOn_of_bounded|theorem tendsto_ofReal|isCompact_preimage'|theorem image_eq_one_of_notMem_mulTSupport|theorem intro \[' in MeasureTheory/Integral/{Lebesgue/Basic,IntegrableOn}.lean, Topology/Instances/ENNReal/Lemmas.lean, Topology/Compactness/Compact.lean, Topology/Algebra/Support.lean`
- `python3 -I: gmt-compare.contract_scope(Contract.lean, 'GMT.Ch08.main_theorem') replay -> namespace GMT.Ch08 + contract opens; lean_contract.validate_lean_statement on the 4 child lean_statements (all OK, unchanged)`
- `lake env lean /tmp/wp-portmanteau-scratch/Stmts.lean (parent type + 4 child types elaborate in the replayed scope)`
- `lake env lean /tmp/wp-portmanteau-final/Final.lean (complete proofs of the 4 exact child statements as GMT.Ch08.Submission.X, comparator-style `exact Submission.X` targets for each, parent assembly of weight_portmanteau_of_radonConverges, #print axioms -> [propext, Classical.choice, Quot.sound])`
- `python3 -I dag.json lean_name scan (no duplicates; 4 proposed names free); git show <each local branch>:GMT/Ch08/Submission.lean | grep -E the 4 proposed names (no matches)`
- `grep -n -i 'liminf\|lim inf\|C_c' book/chapter-08.txt; sed -n 336,385p book/chapter-08.txt (3.7 proof step (3) uses P1 unproved); sed -n 1740,1800p book/chapter-01.txt (4.16 convergence notion)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Portmanteau.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-density-semicontinuity-a1-weight-portmanteau-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/wp-portmanteau-scratch/Stmts.lean`
- `/tmp/wp-portmanteau-final/Final.lean`

Snapshot: project 63436ae6 + Mathlib 25730c7c. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

SimonGMT supplies the varifold API the transfer child needs: structure Varifold, domainMeasure and map_domainMeasure (Varifold.lean:335/347/387); weight = measure.map Prod.fst (:557); weight_finite_on_compact (:576); RadonConverges (VarifoldConvergence.lean:35). Its divergenceDomainTest uses the same lifting pattern (IsInducing.subtypeVal.isCompact_preimage' plus MeasurableEmbedding.integral_map).

Neither SimonGMT nor Mathlib proves a portmanteau for vague convergence. Portmanteau.lean only covers weak convergence of finite/probability measures (FiniteMeasure.limsup_measure_closed_le_of_tendsto :281, ProbabilityMeasure.le_liminf_measure_open_of_tendsto :326), and 'vague' has no match. Chapter 8's 3.7 uses (P1) in step (3) without proof.

Mathlib provides every tool the children use:
- exists_compact_between (LocallyCompact.lean:172)
- exists_continuous_one_zero_of_isCompact (UrysohnsLemma.lean:404)
- Measure.integrableOn_of_bounded (IntegrableOn.lean:716) and integrableOn_iff_integrable_of_support_subset (:462)
- ofReal_integral_eq_lintegral_ofReal (Bochner/Basic.lean:739)
- lintegral_indicator_one (Lebesgue/Basic.lean:572)
- IsOpen.exists_iUnion_isClosed (HausdorffDistance.lean:207)
- Monotone.measure_iUnion and tendsto_measure_iInter_atTop (Measure/Continuity.lean:71, :220)
- IsCompact.exists_cthickening_subset_open, IsCompact.cthickening, closure_eq_iInter_thickening, thickening_mono, self_subset_thickening, thickening_subset_cthickening_of_le (Thickening.lean:426/283/524/88/309/272)
- ENNReal.tendsto_ofReal (ENNReal/Lemmas.lean:72)
- Topology.IsInducing.isCompact_preimage' (Compact.lean:1011)
- HasCompactSupport.intro and image_eq_zero_of_notMem_tsupport (to_additive forms of Support.lean:232 and :111)

All four child lean_statements pass validate_lean_statement and elaborate in the replayed contract scope. In a scratch file that imports GMT.Ch08.Submission, the following compile with axioms propext, Classical.choice and Quot.sound only: complete proofs of all four exact statements, comparator-style exact checks for each, and the parent assembly of the frozen weight_portmanteau_of_radonConverges type. The four proposed bare names do not occur in dag.json or on any local branch.
