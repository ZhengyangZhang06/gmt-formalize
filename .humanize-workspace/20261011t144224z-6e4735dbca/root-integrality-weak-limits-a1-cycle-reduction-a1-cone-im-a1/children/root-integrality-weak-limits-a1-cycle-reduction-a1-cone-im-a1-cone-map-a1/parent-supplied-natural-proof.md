# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.cone_map-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 4 and 6 of the parent proof (h(Φ(s, x)) = s x is C^∞; Dh(Φ(s, x))(Φ(σ, w)) = σ x + s w, so Dh(Φ(s, x)) e_0 = x and Dh(Φ(s, x))(ι v) = s v; multilinearity), filled in.

Notation (used throughout): E := ℝ^P = Eucl P and E′ := ℝ^{P+1} = Eucl (P + 1), with the Euclidean norms; Φ(s, x) := (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x)) ∈ E′ for s ∈ ℝ, x ∈ E, so Φ(s, x)_0 = s and Φ(s, x)_{j+1} = x_j (j ∈ Fin P); e_0 := EuclideanSpace.single 0 1 ∈ E′; ι(w) := Φ(0, w) for w ∈ E; π(y) := (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ E for y ∈ E′, so π(y)_j = y_{j+1}; y_0 := y 0 (= y.ofLp 0). D^k(E) := TestFormOn univ k (C^∞ k-forms with compact tsupport), D_k(E) := GeometricCurrentOn univ k; C^∞ means ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞), i.e. smooth of every finite order. Let p_0(y) := y_0 and h(y) := p_0(y) • π(y).

1. (Linear pieces.) p_0 : ℝ^{P+1} → ℝ is a continuous linear functional (it is EuclideanSpace.proj 0). π is ℝ-linear, since π(y)_j = y_{j+1} coordinatewise, hence a continuous linear map π_L : ℝ^{P+1} →L[ℝ] ℝ^P (finite dimension; or explicitly the composite of the continuous linear equivalences EuclideanSpace.equiv with the continuous linear map w ↦ (j ↦ w (Fin.succ j)) = Fin.tail). So h(y) = p_0(y) • π_L(y).
2. (Smoothness.) Continuous linear maps are C^∞, so h = p_0 • π_L is C^∞ (ContDiff.smul).
3. (Values on Φ.) Φ(s, x)_0 = (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x)) 0 = s, and π(Φ(s, x)) = (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) = (EuclideanSpace.equiv (Fin P) ℝ).symm (EuclideanSpace.equiv (Fin P) ℝ x) = x (ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons, ContinuousLinearEquiv.symm_apply_apply). Hence h(Φ(s, x)) = s • x.
4. (Derivative.) p_0 and π_L have derivatives p_0 and π_L at every point. By the product rule for scalar times vector (HasFDerivAt.smul), h has derivative D_y := p_0(y) • π_L + p_0.smulRight (π_L y) at y, so fderiv ℝ h y w = y_0 • π(w) + w_0 • π(y) for all w ∈ ℝ^{P+1}. Take y := Φ(s, x); by step 3, y_0 = s and π(y) = x.
   • e_0 = EuclideanSpace.single 0 1 has (e_0)_0 = 1 and π(e_0) = 0 (all its coordinates j + 1 vanish), so D_y e_0 = s • 0 + 1 • x = x.
   • ι(v) = Φ(0, v) has ι(v)_0 = 0 and π(ι(v)) = v (step 3 with s = 0), so D_y(ι v) = s • v + 0 • x = s • v.
5. (Pull-back identity.) Let α be an (m+1)-covector on ℝ^P and v : Fin m → ℝ^P. Then (α.compContinuousLinearMap D_y)(Fin.cons e_0 (fun i => ι(v i))) = α(D_y ∘ Fin.cons e_0 (fun i => ι(v i))) = α(Fin.cons (D_y e_0) (fun i => D_y(ι(v i)))) (Fin.comp_cons) = α(Fin.cons x (fun i => s • v i)) (step 4). With c := Fin.cons (1 : ℝ) (fun _ : Fin m => s) : Fin (m + 1) → ℝ we have Fin.cons x (fun i => s • v i) = (fun j => c j • Fin.cons x v j) (check j = 0 and j = Fin.succ i via Fin.cases), so ContinuousAlternatingMap.map_smul_univ gives α(Fin.cons x (fun i => s • v i)) = (∏_j c j) • α(Fin.cons x v) = (1 · s^m) α(Fin.cons x v) (Fin.prod_univ_succ; the product of the constant s over Fin m is s^m). Hence the left side equals s^m * α(Fin.cons x v). (For m = 0 both sides are α(Fin.cons x v), as s^0 = 1.)
6. Steps 2, 3 and 5 are the three asserted facts. ∎

## Key steps

1. y ↦ y_0 and π are continuous linear maps, so h = y_0 • π(y) is C^∞ and h(Φ(s,x)) = s x.
2. Product rule: Dh(y)(w) = y_0 π(w) + w_0 π(y); at y = Φ(s,x) this maps e_0 ↦ x and ι(v) ↦ s v.
3. Hence (α ∘ Dh(Φ(s,x)))(e_0, ιv) = α(x, s v_1, …, s v_m) = s^m α(x, v) by multilinearity (map_smul_univ).

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
