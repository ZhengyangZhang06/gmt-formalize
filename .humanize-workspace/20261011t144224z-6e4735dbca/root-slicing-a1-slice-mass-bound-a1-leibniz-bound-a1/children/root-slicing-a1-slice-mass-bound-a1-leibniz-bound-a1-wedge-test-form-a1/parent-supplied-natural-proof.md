# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1`
- Child DAG node: `root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1.wedge_test_form-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 2(a), (b), (d) for the form η₃ = Dψ∧ω, stated for an arbitrary C^∞ field α of continuous linear functionals. The parent applies it with α = Dψ = fderiv ℝ ψ, which is C^∞ by `ContDiff.fderiv_right` because ψ is C^∞.

Setting. P, m ∈ ℕ and U ⊆ ℝ^P. ω ∈ D^m(U) = TestFormOn U m, i.e. ω is C^∞, has compact support and satisfies tsupport ω ⊆ U. α : ℝ^P → (ℝ^P →L[ℝ] ℝ) is C^∞. For x ∈ ℝ^P, (α(x)).smulRight(ω(x)) is the continuous linear map h ↦ α(x)(h)·ω(x) from ℝ^P to Λ^m(ℝ^P), and alternatizeUncurryFin turns it into an (m+1)-covector. For a form g, support g := {x : g(x) ≠ 0} and tsupport g := closure(support g).

1. (Candidate.) Define η(x) := alternatizeUncurryFin((α(x)).smulRight(ω(x))) ∈ Λ^{m+1}(ℝ^P). An element of TestFormOn U (m+1) is an (m+1)-form together with proofs that it is C^∞, has compact support and has tsupport ⊆ U. So it suffices to prove these three properties (steps 2–4); the pointwise formula then holds by definition.

2. (Smoothness.) α and ω are C^∞. The map (ℓ, γ) ↦ ℓ.smulRight γ from (ℝ^P →L ℝ) × Λ^m(ℝ^P) to (ℝ^P →L Λ^m(ℝ^P)) is continuous bilinear, so x ↦ (α(x)).smulRight(ω(x)) is C^∞ (`ContDiff.smulRight`). alternatizeUncurryFin is the underlying function of the continuous linear map `ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ` (`ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply`), and continuous linear maps are C^∞ (`ContinuousLinearMap.contDiff`). A composition of C^∞ maps is C^∞ (`ContDiff.comp`), so η is C^∞.

3. (Support.) If ω(x) = 0, then (α(x)).smulRight 0 = 0 (`ContinuousLinearMap.smulRight_zero`), and alternatizeUncurryFin(0) = 0 because it is linear (`map_zero` for alternatizeUncurryFinCLM). So η(x) = 0. Hence support η ⊆ support ω.

4. (Compact support and support in U.) By step 3, η has compact support because ω has (`HasCompactSupport.mono`). Taking closures in step 3 (`closure_mono`) gives tsupport η ⊆ tsupport ω ⊆ U.

5. (Conclusion.) By steps 2 and 4, η ∈ D^{m+1}(U), and η(x) = alternatizeUncurryFin((α(x)).smulRight(ω(x))) for every x. ∎

## Key steps

1. Define η(x) := alternatizeUncurryFin((α x).smulRight(ω x)); x ↦ (α x).smulRight(ω x) is C^∞ by ContDiff.smulRight, and composing with the continuous linear map alternatizeUncurryFinCLM keeps it C^∞.
2. ω(x) = 0 implies (α x).smulRight 0 = 0 and alternatizeUncurryFin 0 = 0, so support η ⊆ support ω.
3. Hence η has compact support and tsupport η ⊆ tsupport ω ⊆ U; package η as an element of TestFormOn U (m+1).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886 = workspace HEAD; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (both identical)`
- `grep -n 'theorem\|lemma\|def \|abbrev ' local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean (extDeriv, extDeriv_add, extDeriv_smul/extDeriv_fun_smul only for a constant c : 𝕜)`
- `rg -n 'smul|wedge|Leibniz|product' local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/ ; rg -n 'extDeriv.*smul|smul.*extDeriv' local-references/197bdd4b88278494/mathlib/Mathlib (constant-scalar lemmas only)`
- `grep -n 'covectorEuclideanNorm|abbrev Covector|abbrev DifferentialForm|def IsTestForm|abbrev exteriorDerivative|abbrev TestFormOn|structure GeometricCurrentOn|boundary_apply|tsupport_exteriorDerivative_subset|abbrev NVector|exteriorDerivative_isTestForm' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `grep -n 'theorem\|lemma\|^def \|^abbrev ' simongmt/Poincare/SimonGMT/Chapter06/{WedgeForms,Representation,CurrentLocalEquality,FormsDuality}.lean (no function-multiplier Leibniz rule, no smooth-multiplier closure of TestFormOn, no representation mass estimate)`
- `rg -n 'theorem enorm_integral_le_lintegral_enorm|theorem ContDiff.smulRight|theorem tsupport_smul_subset_right|def alternatizeUncurryFinCLM|theorem alternatizeUncurryFin_add|theorem alternatizeUncurryFin_smul' local-references/197bdd4b88278494/mathlib/Mathlib ; rg -n 'theorem extDeriv.*smul|fderiv_fun_smul' .../DifferentialForm/Basic.lean .../FDeriv/Mul.lean`
- `rg -c 'slicing_mb_lb' local-references/197bdd4b88278494/project lake-packages-25730c7c/simongmt/Poincare local-references/197bdd4b88278494/mathlib/Mathlib (no match, exit 1)`
- `python3 scan of dag.json (217 nodes): collision check for lean_names slicing_mb_lb_{extDeriv_smul,smul_testForm,wedge_testForm,repr_bound} and keys under leibniz_bound-a1 (none); search of lean_statements/titles for smulRight, alternatizeUncurryFin, extDeriv, exteriorDerivative, covectorEuclideanNorm, IsMeasureRepresentation (no identical statement; cmb_measureRepresentation_continuous_bound and smr_ofReal_integral_le_massOn differ)`
- `lake env printenv LEAN_PATH; lean -o /tmp/lb_split_Vd4laa/out/GMT/Ch06/Submission.olean GMT/Ch06/Submission.lean`
- `lean /tmp/lb_split_Vd4laa/check/Names.lean (#check fderiv_fun_smul, ContDiff.smul, ContDiff.smulRight, ContDiff.fderiv_right, alternatizeUncurryFinCLM(_apply), alternatizeUncurryFin_add/_smul, enorm_integral_le_lintegral_enorm, Real.enorm_eq_ofReal_abs, exteriorDerivative_isTestForm, tsupport_exteriorDerivative_subset, exteriorDerivativeTestOn, HasCompactSupport.mono, tsupport_smul_subset_right, ContinuousLinearMap.smulRight_zero)`
- `python3 /tmp/lb_split_Vd4laa/scripts/gen.py (gmt-compare.py child_modules, contract mode) ; lean /tmp/lb_split_Vd4laa/cmp/{extderiv_leibniz,smul_test_form,wedge_test_form,repr_bound}_{Challenge,Solution}.lean`
- `lean /tmp/lb_split_Vd4laa/check/Assembly2.lean (#print axioms HumanizeNodeComparator.assembly)`
- `lean /tmp/lb_split_Vd4laa/check/Instances.lean (pp.explicit smul instance; IsSmoothForm index by rfl)`
- `python3: sha256(json.dumps(target, sort_keys=True, separators=(',',':'), ensure_ascii=False)) reproduces decomposition-scope-v1.json digest of root.compactness_mass_bounds-a1.repr_bound-a1; recomputed for this node from dag.json and parent-child-handoff.json`
- `sed -n '1340,1415p' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt (Simon 4.9–4.11)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/WedgeForms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Representation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-repr-bound-a1/decomposition-scope-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/lb_split_Vd4laa/check/Names.lean`
- `/tmp/lb_split_Vd4laa/check/Full.lean`
- `/tmp/lb_split_Vd4laa/check/Instances.lean`
- `/tmp/lb_split_Vd4laa/check/Assembly2.lean`
- `/tmp/lb_split_Vd4laa/cmp/extderiv_leibniz_Solution.lean`
- `/tmp/lb_split_Vd4laa/cmp/smul_test_form_Solution.lean`
- `/tmp/lb_split_Vd4laa/cmp/wedge_test_form_Solution.lean`
- `/tmp/lb_split_Vd4laa/cmp/repr_bound_Solution.lean`

The pinned snapshot (project d8d46c95, which is the workspace HEAD; Mathlib 25730c7c) contains the frozen Ch06 contract, byte-identical to the workspace Submission.

What is missing from the libraries:
- Mathlib has extDeriv = alternatizeUncurryFin ∘ fderiv, but extDeriv_smul only for constant scalars. The function-multiplier Leibniz rule d(ψω) = ψ dω + Dψ∧ω is absent.
- SimonGMT supplies exteriorDerivative, exteriorDerivativeTestOn, exteriorDerivative_isTestForm, tsupport_exteriorDerivative_subset, GeometricCurrentOn.boundary_apply and covectorEuclideanNorm. It has no closure of TestFormOn under smooth multiplication or wedge with a smooth 1-form, and no representation mass estimate.

Every Mathlib lemma cited in the child proofs exists at the pinned revision: fderiv_fun_smul, ContDiff.smul, ContDiff.smulRight, ContDiff.fderiv_right, alternatizeUncurryFinCLM(_apply), alternatizeUncurryFin_add/_smul, ContinuousLinearMap.smulRight_zero, tsupport_smul_subset_right, HasCompactSupport.smul_left/mono, enorm_integral_le_lintegral_enorm, Real.enorm_eq_ofReal_abs, lintegral_mono.

No proposed name occurs in the snapshot, SimonGMT, Mathlib or the 217 DAG nodes, and no DAG node has an identical type.

In the verifier-generated comparator child scope, all four child types elaborate and have scratch proofs with axioms [propext, Classical.choice, Quot.sound]. The exact frozen parent type follows from the four exact child strings plus the frozen slicing_mb_wedge_norm_le type with the same axioms.

Simon's printed 4.11 matches the Leibniz/boundary identity used.
