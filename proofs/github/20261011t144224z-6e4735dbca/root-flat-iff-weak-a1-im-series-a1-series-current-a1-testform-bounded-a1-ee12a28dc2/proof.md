# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.im_series-a1.series_current-a1`
- Child DAG node: `root.flat_iff_weak-a1.im_series-a1.series_current-a1.testform_bounded-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Write ω also for the underlying form (ω : DifferentialForm (Eucl P) n) : Eucl P → Covector (Eucl P) n.

1. ω is smooth and has compact support.
   - The membership proof ω.property : ω ∈ TestFormOn U n = testFormOnSubmodule U n says IsTestForm ω ∧ tsupport ω ⊆ U.
   - Its first component IsTestForm ω is IsSmoothForm ω ∧ HasCompactSupport ω.
   - IsSmoothForm ω is by definition ContDiff ℝ ∞ ω, with ∞ the smoothness order in WithTop ℕ∞.
   Lean remark: in the contract scope, `open scoped ENNReal` makes a bare `∞` elaborate as the ℝ≥0∞ infinity. So keep this hypothesis as `IsSmoothForm ω` (from ω.property.1.1) and apply `ContDiff.continuous` to it; the definition unfolds by defeq.
2. A ContDiff map is continuous (ContDiff.continuous). A continuous map with compact support into a normed group is bounded (HasCompactSupport.exists_bound_of_continuous, the additive form of HasCompactMulSupport.exists_bound_of_continuous). So there is B ∈ ℝ with ‖ω(x)‖ ≤ B for all x. In particular 0 ≤ ‖ω(0)‖ ≤ B (norm_nonneg).
3. Put D := √(P^n), so D ≥ 0 (Real.sqrt_nonneg), and C := D·B + 1. Since D ≥ 0 and B ≥ 0, C ≥ 1 > 0 (positivity).
4. Let x ∈ ℝ^P.
   - The sibling covector_norm (Submission.fiw_ims_sc_covectorNorm_le_opNorm P n (ω x)) gives covectorEuclideanNorm(ω(x)) ≤ D·‖ω(x)‖.
   - Since D ≥ 0 and ‖ω(x)‖ ≤ B: D·‖ω(x)‖ ≤ D·B (mul_le_mul_of_nonneg_left), and D·B ≤ D·B + 1 = C (linarith).
   - Hence covectorEuclideanNorm(ω(x)) ≤ C for every x, and C > 0 by step 3. ∎

## Key steps

1. ω.property.1 : IsTestForm ω gives IsSmoothForm ω (ContDiff ℝ ∞) and HasCompactSupport ω
2. ContDiff.continuous and HasCompactSupport.exists_bound_of_continuous: ‖ω(x)‖ ≤ B for all x, with B ≥ 0
3. covector_norm: |ω(x)| ≤ √(P^n)·‖ω(x)‖ ≤ √(P^n)·B ≤ √(P^n)·B + 1 =: C > 0

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `diff project/GMT/Ch06/Contract.lean project/GMT/Ch06/Submission.lean (IDENTICAL)`
- `grep -n 'def covectorEuclideanNorm|def massAdmissibleOn|massOn|le_massOn|structure GeometricCurrentOn|def TestFormOnConverges|abbrev TestFormOn|def testFormOnSubmodule|abbrev Covector|abbrev DifferentialForm|def IsSmoothForm|def IsTestForm|instance.*CoeFun' SimonGMT/Chapter06/*.lean`
- `grep -n '^(public )?import' SimonGMT/Chapter06/*.lean; grep -n '^theorem|^lemma|^def|^abbrev|^structure|^instance' FormSupNorm.lean CurrentLocalEquality.lean FixedSupportCurrentTopology.lean`
- `python3 scan of dag.json (207 nodes) lean_name/lean_statement and nodes/*/decomposition-v*.json (193 files) for fiw_ims_sc_* and for statements mentioning covectorEuclideanNorm with a norm, or TestFormOnConverges`
- `rg Mathlib snapshot: exists_open_between_and_isCompact_closure, HasCompactMulSupport.exists_bound_of_continuous, ContinuousAlternatingMap.le_opNorm, EuclideanSpace.basisFun_apply, norm_iteratedFDeriv_zero, iteratedFDeriv_fun_zero, Metric.tendstoUniformlyOn_iff, image_eq_zero_of_notMem_tsupport, ENNReal.summable_toReal, ENNReal.tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg, norm_tsum_le_tsum_norm, Summable.of_abs, Int.natCast_natAbs, Int.cast_abs`
- `git archive d8d46c9 | tar -x -C /tmp/sc_v2.rJJTMk; ln -s lake-packages-25730c7c .lake/packages; lake build GMT.Ch06.Submission (Build completed successfully, 3152 jobs)`
- `python3 gmt-compare.contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') and lean_contract.validate_lean_statement on the 5 child types`
- `lake env lean Scratch/ChildTypes.lean (5 child types + parent + mass_bound elaborate in comparator scope)`
- `lake env lean Scratch/Proofs.lean (#print axioms: 5 children and assembly = [propext, Classical.choice, Quot.sound])`
- `lake env lean Scratch/Comparator.lean (exact Submission.X closes each frozen child type; exact frozen parent derived from children + fiw_ims_mass_bound stub; sorryAx only from the stub)`
- `grep -n 'lean_name' /runtime/flows/gmt-claude-0135a42af877/_recursive_lean/runtime.py; sed -n 6480,6560p (_existing_lean_name_problem)`
- `python3 read of issue-workers.json and dag.json entry for this node (attempt 2, children = []); read of decomposition-v1.json, decomposition-audit-v1.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FixedSupportCurrentTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/InfiniteSum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/Group/Unbundled/Int.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/Ring/Cast.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-series-current-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-series-current-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-series-current-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-0135a42af877/_recursive_lean/runtime.py`
- `/tmp/sc_v2.rJJTMk/Scratch/ChildTypes.lean`
- `/tmp/sc_v2.rJJTMk/Scratch/Proofs.lean`
- `/tmp/sc_v2.rJJTMk/Scratch/Comparator.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract; Contract.lean and Submission.lean are identical.

The pinned SimonGMT Chapter06 provides only the definitions used here: covectorEuclideanNorm, massAdmissibleOn, massOn and le_massOn, TestFormOn/testFormOnSubmodule, TestFormOnConverges, and GeometricCurrentOn with its sequential-continuity field. It has none of the five needed facts:
- no comparison of covectorEuclideanNorm with the operator norm;
- no test-form boundedness lemma;
- no null-sequence smallness lemma and no bound-implies-continuity criterion;
- no integer-weighted series estimate.
FormSupNorm.lean only defines testFormEuclideanSupNorm and is not imported by the contract. CurrentLocalEquality and FixedSupportCurrentTopology contain nothing applicable. The only related DAG lemma, isoperimetric_abs_covector_apply_le, is the converse inequality. So the five facts become the children.

Mathlib supplies every tool cited in the child proofs:
- exists_open_between_and_isCompact_closure;
- the additive form of HasCompactMulSupport.exists_bound_of_continuous;
- ContinuousAlternatingMap.le_opNorm and EuclideanSpace.basisFun_apply;
- norm_iteratedFDeriv_zero and iteratedFDeriv_fun_zero;
- Metric.tendstoUniformlyOn_iff and image_eq_zero_of_notMem_tsupport;
- ENNReal.summable_toReal, ENNReal.tsum_mul_left and ENNReal.ofReal_tsum_of_nonneg;
- norm_tsum_le_tsum_norm and Summable.of_abs;
- Int.natCast_natAbs and Int.cast_abs.

Gotcha: in the contract scope a bare ∞ elaborates as the ℝ≥0∞ infinity, so smoothness must be kept as IsSmoothForm.

Fresh scratch build of the frozen commit:
- all 5 child types elaborate in the comparator scope;
- complete child proofs compile with axioms [propext, Classical.choice, Quot.sound];
- exact Submission.X closes each frozen type;
- the exact frozen parent follows from the children plus the fiw_ims_mass_bound contract, with sorryAx only from that stub.

No fiw_ims_sc_* name is a DAG node (207 nodes scanned). The only proposal using these names is this node's own unregistered v1, and the flow's _existing_lean_name_problem checks DAG nodes only.
