# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.im_series-a1.series_current-a1`
- Child DAG node: `root.flat_iff_weak-a1.im_series-a1.series_current-a1.covector_norm-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation:
- b_i := EuclideanSpace.basisFun (Fin P) ℝ i for i : Fin P.
- For I : Fin n → Fin P, v_I := (i ↦ b_{I(i)}) : Fin n → Eucl P.
- t_I := (α v_I)² if StrictMono I, and t_I := 0 otherwise.
Unfolding the definition (unfold covectorEuclideanNorm), covectorEuclideanNorm α = √(Σ_I t_I). The sum runs over the finite type Fin n → Fin P.

1. Each b_i is a unit vector: b_i = EuclideanSpace.single i 1 (EuclideanSpace.basisFun_apply), and ‖EuclideanSpace.single i 1‖ = ‖(1 : ℝ)‖ = 1 (simp). Hence ∏_{i : Fin n} ‖b_{I(i)}‖ = 1 for every I.
2. For every I, ContinuousAlternatingMap.le_opNorm gives ‖α v_I‖ ≤ ‖α‖·∏_i ‖b_{I(i)}‖, which equals ‖α‖ by step 1. On ℝ, ‖·‖ = |·| (Real.norm_eq_abs), so |α v_I| ≤ ‖α‖.
3. For every I, t_I ≤ ‖α‖².
   - If StrictMono I: t_I = (α v_I)² = |α v_I|² (sq_abs) ≤ ‖α‖², by step 2 and 0 ≤ |α v_I| (pow_le_pow_left₀).
   - Otherwise: t_I = 0 ≤ ‖α‖² (positivity).
4. The type Fin n → Fin P has P^n elements (Fintype.card_fun, Fintype.card_fin). By Finset.sum_le_sum and step 3: Σ_I t_I ≤ Σ_I ‖α‖² = P^n·‖α‖² (Finset.sum_const, Finset.card_univ; simp [Finset.card_univ] closes this equality).
5. Real.sqrt is monotone (Real.sqrt_le_sqrt), so covectorEuclideanNorm α = √(Σ_I t_I) ≤ √(P^n·‖α‖²).
6. Since P^n ≥ 0, √(P^n·‖α‖²) = √(P^n)·√(‖α‖²) (Real.sqrt_mul). Since ‖α‖ ≥ 0, √(‖α‖²) = ‖α‖ (Real.sqrt_sq, norm_nonneg). With step 5: covectorEuclideanNorm α ≤ √(P^n)·‖α‖.

No case distinction is needed:
- for n = 0 the index type has exactly one element and the empty product in step 1 is 1;
- for P = 0 < n the index type is empty and both sides are 0. ∎

## Key steps

1. unfold covectorEuclideanNorm α = √(Σ_I t_I) over I : Fin n → Fin P
2. basis vectors are unit vectors; ContinuousAlternatingMap.le_opNorm gives |α(b_{I(0)},…,b_{I(n−1)})| ≤ ‖α‖, hence t_I ≤ ‖α‖²
3. card(Fin n → Fin P) = P^n gives Σ_I t_I ≤ P^n·‖α‖²
4. Real.sqrt_le_sqrt, then √(P^n·‖α‖²) = √(P^n)·‖α‖ (Real.sqrt_mul, Real.sqrt_sq)

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
