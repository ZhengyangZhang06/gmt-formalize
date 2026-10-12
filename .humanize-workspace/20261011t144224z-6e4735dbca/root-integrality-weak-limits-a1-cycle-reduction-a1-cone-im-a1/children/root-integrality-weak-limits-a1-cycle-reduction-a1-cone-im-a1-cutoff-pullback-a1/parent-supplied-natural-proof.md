# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.cutoff_pullback-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 5 (A good η) of the parent proof, first half (h^#ω is C^∞ and the cut-off has compact support), stated for an arbitrary C^∞ map f and cut-off χ; the parent applies it with f := h and χ(y) := ϑ(y_0) ζ(π y).

Notation: C^∞ means ContDiff ℝ ∞ with ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞); p(y) := (ω(f y)).compContinuousLinearMap (fderiv ℝ f y), a k-covector on ℝ^P.

1. (Df is C^∞.) f is C^∞ and ∞ + 1 ≤ ∞, so y ↦ fderiv ℝ f y is C^∞ (ContDiff.fderiv_right).
2. (ω ∘ f is C^∞.) ω and f are C^∞, so y ↦ ω(f y) is C^∞ (ContDiff.comp).
3. (The pull-back operator is C^∞.) Let 𝒫(B) := ContinuousAlternatingMap.compContinuousLinearMapCLM B for B : ℝ^P →L[ℝ] ℝ^Q; it is the continuous linear map α ↦ α.compContinuousLinearMap B from k-covectors on ℝ^Q to k-covectors on ℝ^P. By ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM (with s := univ), 𝒫 is analytic on the whole space, hence C^∞ (AnalyticOnNhd.contDiff).
4. (p is C^∞.) p(y) = 𝒫(fderiv ℝ f y)(ω(f y)). By steps 1–3, y ↦ 𝒫(fderiv ℝ f y) is a C^∞ family of continuous linear maps and y ↦ ω(f y) is C^∞, so p is C^∞ (ContDiff.clm_apply).
5. (η is a test form.) Define η(y) := χ(y) • p(y). η is C^∞ (ContDiff.smul). χ has compact support, hence so does χ • p (HasCompactSupport.smul_right), and tsupport η ⊆ univ. So η satisfies IsTestForm (C^∞ and compact support) and lies in TestFormOn univ k.
6. By construction η(y) = χ(y) • (ω(f y)).compContinuousLinearMap (fderiv ℝ f y) for every y. ∎

## Key steps

1. y ↦ Df(y) (ContDiff.fderiv_right) and y ↦ ω(f(y)) are C^∞.
2. B ↦ compContinuousLinearMapCLM B is analytic (Mathlib analyticOnNhd_compContinuousLinearMapCLM), hence C^∞, so p(y) = compContinuousLinearMapCLM (Df y) (ω(f y)) is C^∞ (ContDiff.clm_apply).
3. χ • p is C^∞ with compact support inherited from χ, hence a test form on univ with the stated values.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; sha256sum GMT/Ch06/Contract.lean`
- `python3 -I: read nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1/{parent-child-handoff.json,parent-supplied-natural-proof.md,parent-supplied-plan.md} and nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v2.json (reused-child format)`
- `python3 -I: dag.json status and frozen lean_statement of iwl_cr_cone_integer_multiplicity, iwl_cr_interval_product_im, iwl_cr_radial_operator, isoperimetric_apply_eq_zero_of_disjoint_support, iwl_sp_exists_compatible_testForm, slicing_mb_lb_smul_testForm, fiw_tb_ext_smul_testForm, iwl_sp_sn_signed_simpleNVector_bound_ne_zero, cmb_abs_apply_le_of_massOn_le`
- `python3 -I: collision scan of dag.json and nodes/*/decomposition-v*.json for the 7 proposed lean_names and the prefix iwl_cr_ci_`
- `grep -rn compContinuousLinearMap mathlib/Mathlib --include=*.lean | grep -i 'contDiff|hasStrictFDeriv|hasFDeriv|differentiable'`
- `grep -rn 'def curryLeft|theorem curryLeft_apply|curryLeftLI|analyticOnNhd_compContinuousLinearMapCLM' mathlib/Mathlib/Analysis/Normed/Module/Alternating mathlib/Mathlib/Analysis/Analytic mathlib/Mathlib/LinearAlgebra/Alternating`
- `grep -n 'theorem|lemma' mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean; grep -rn 'contDiff_comp_iff|comp_contDiff_iff' mathlib/Mathlib`
- `grep -rn 'theorem Integrable.mul_prod|integrable_prod_iff' mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `grep -n '^theorem|^def|^abbrev|^structure' simongmt Chapter06/{Forms,Currents,Mass,FormsDuality,CurrentLocalEquality,Product,AffineCurrentPushforward,ParametricCurrentContinuity,GeometricPointProduct,FixedSupportCurrentTopology}.lean`
- `grep -rn 'ContDiff.*ullback|ullback.*isSmoothForm|integral_integral_swap' simongmt/Poincare/SimonGMT/Chapter06`
- `python3 -I /tmp/ci_decomp/scripts/gen.py (verifier gmt-compare.py child_modules in contract scope + lean_contract.validate_lean_statement) -> /tmp/ci_decomp/gen2/*__NodeChallenge.lean`
- `lake env lean on each of the 7 generated NodeChallenge files and on /tmp/ci_decomp/probe/AllChallenges.lean`
- `lake env lean /tmp/ci_decomp/probe/Assembly2.lean (frozen parent type from sorry-stubbed children and dependencies, #print axioms)`
- `lake env lean /tmp/ci_decomp/probe/Names.lean (#check of the cited Mathlib/SimonGMT declarations)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-vanish-off-support-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-vanish-off-support-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-compatible-form-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Analytic/CPolynomial.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/ParametricCurrentContinuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ci_decomp/scripts/gen.py`
- `/tmp/ci_decomp/probe/AllChallenges.lean`
- `/tmp/ci_decomp/probe/Assembly2.lean`
- `/tmp/ci_decomp/probe/Names.lean`

Snapshot identity:
- Project d8d46c95, Mathlib 25730c7c.
- The snapshot's Ch06 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 ea3ee0ddd08be5db…).

DAG findings:
- isoperimetric_apply_eq_zero_of_disjoint_support is accepted with exactly the type reused here.
- The frozen types of this node's dependencies iwl_cr_interval_product_im and iwl_cr_radial_operator were used verbatim in the assembly.
- The compatible-form construction of another branch (iwl_sp_exists_compatible_testForm) is only rlcr-lean, so it is not reused.
- No existing node supplies hyperplane slices, product-current support, the cone-map derivative or a Fubini exchange for τ(M,θ,ξ).
- The prefix iwl_cr_ci_ is unused anywhere in dag.json or the decomposition files.

Library findings:
- No ContDiff lemma for compContinuousLinearMap in Mathlib; there are only HasFDerivAt/Differentiable versions in FDeriv/ContinuousAlternatingMap.lean.
- Mathlib CPolynomial.lean:271 has ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM, which with AnalyticOnNhd.contDiff gives smoothness of the pull-back.
- Alternating/Curry.lean has curryLeft, curryLeft_apply_apply and curryLeftLI.
- MeasureTheory/Integral/Prod.lean has integral_integral_swap and Integrable.mul_prod. Integrable.prod_mul does not exist; this was corrected.
- SimonGMT has only affine pull-back smoothness (affinePullbackForm_isSmoothForm) and pointSlice_isTestForm, which is the model for slice_forms. It has no nonlinear pull-back smoothness and no current/integral exchange; ParametricCurrentContinuity only proves continuity of parameter-slice values.

Lean checks:
- All 7 child statements elaborate in the comparator's exact challenge form.
- The sorry-stubbed assembly proves the byte-identical frozen parent type with no errors.
- Every other cited declaration name type-checks.
