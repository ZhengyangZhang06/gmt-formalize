# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_homotopy-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_homotopy-a1.degree_zero-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Part (b), Steps 8–10, of the supplied proof (“H(dφ)(x) = ∫_0^1 (d/dt)φ(tx) dt = φ(x) − φ(0)”), written out in full.

Notation. E := ℝ^P, D := fderiv ℝ, d := extDeriv.

1. (Reduction.) Fix x ∈ E. χ(x) and φ(x) − φ(0) are continuous alternating 0-linear maps on E. By extensionality (ext) it suffices to show, for every v : Fin 0 → E, that χ(x)(v) = (φ(x) − φ(0))(v) = φ(x)(v) − φ(0)(v) (ContinuousAlternatingMap.sub_apply).
2. (Degree-0 exterior derivative.) Fix t ∈ ℝ. By the definition extDeriv φ y = alternatizeUncurryFin (Dφ(y)) and ContinuousAlternatingMap.alternatizeUncurryFin_apply, dφ(t x)(Fin.cons x v) = Σ_{i ∈ Fin 1} (−1)^i • Dφ(t x)[(Fin.cons x v)_i](removeNth i (Fin.cons x v)). Fin 1 has the single element 0 (Fin.sum_univ_one). Since (−1)^0 = 1 (one_smul) and (Fin.cons x v)_0 = x (Fin.cons_zero), the sum equals Dφ(t x)[x](removeNth 0 (Fin.cons x v)). The type Fin 0 → E is a subsingleton, so removeNth 0 (Fin.cons x v) = v (congr / Subsingleton.elim). Hence dφ(t x)(Fin.cons x v) = Dφ(t x)[x](v) for every t.
3. (Rewrite the hypothesis.) By the hypothesis on χ, Step 2 and t^0 = 1 (pow_zero, one_mul), χ(x)(v) = ∫_0^1 Dφ(t x)[x](v) dt.
4. (Derivative and continuity.) φ is C^∞ of order ≥ 1, so it is differentiable with continuous derivative (ContDiff.differentiable, ContDiff.continuous_fderiv). Fix t. The map s ↦ s•x has derivative x at t, so by the chain rule s ↦ φ(s x) has derivative Dφ(t x)[x] at t (HasFDerivAt.comp_hasDerivAt). Composing with the continuous linear evaluation at v (ContinuousAlternatingMap.apply ℝ E ℝ v), g(s) := φ(s x)(v) has derivative Dφ(t x)[x](v) at t. The map t ↦ Dφ(t x)[x](v) is continuous, being built from t ↦ t•x, Dφ, application to x and evaluation at v (Continuous.clm_apply, Continuous.eval_const). Hence it is interval integrable on [0, 1].
5. (Fundamental theorem of calculus.) By intervalIntegral.integral_eq_sub_of_hasDerivAt, ∫_0^1 Dφ(t x)[x](v) dt = g(1) − g(0) = φ(1•x)(v) − φ(0•x)(v) = φ(x)(v) − φ(0)(v) (one_smul, zero_smul).
6. (Conclusion.) Steps 3 and 5 give χ(x)(v) = φ(x)(v) − φ(0)(v) for every v : Fin 0 → E. By Step 1, χ(x) = φ(x) − φ(0). Since x was arbitrary, this holds for every x. ∎

## Key steps

1. Reduce by ext to χ(x)(v) = φ(x)(v) − φ(0)(v) for v : Fin 0 → E.
2. dφ(t x)(cons x v) = Dφ(t x)[x](v): unfold extDeriv, apply alternatizeUncurryFin_apply and Fin.sum_univ_one, and use that Fin 0 → E is a subsingleton.
3. With t^0 = 1, χ(x)(v) = ∫_0^1 Dφ(t x)[x](v) dt.
4. g(s) = φ(s x)(v) has the continuous derivative Dφ(t x)[x](v) (chain rule, evaluation as a continuous linear map).
5. FTC on [0,1] gives φ(x)(v) − φ(0)(v); conclude χ(x) = φ(x) − φ(0).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (project_commit d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; sha256sum GMT/Ch06/Contract.lean`
- `grep -rn 'theorem alternatizeUncurryFin_apply|theorem alternatizeUncurryFin_curryLeft|def alternatizeUncurryFin|theorem extDeriv_apply|def extDeriv\b|theorem curryLeft_apply_apply|theorem cons_comp_succ_succAbove|theorem removeNth_zero|theorem integral_eq_sub_of_hasDerivAt\b|theorem integral_finsetSum|theorem integral_finset_sum' <snapshot>/mathlib/Mathlib`
- `grep -rn 'continuous_eval_const|theorem apply_apply|def apply |continuousAlternatingMap_apply' <snapshot>/mathlib/Mathlib/Topology/Algebra/Module/Alternating/*.lean <snapshot>/mathlib/Mathlib/Analysis/Normed/Module/Alternating/*.lean <snapshot>/mathlib/Mathlib/Analysis/Calculus/FDeriv/*.lean`
- `rg -n -i 'radial homotopy|poincare_lemma|poincaré lemma|homotopy formula|coneOperator|radialHomotopy' <snapshot>/mathlib/Mathlib <snapshot>/project/GMT`
- `rg -n -i 'radial|homotopy formula|alternatizeUncurryFin_curryLeft|cons_comp_succ_succAbove' lake-packages-25730c7c/simongmt/Poincare; grep -rn 'DifferentialForm\b' simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `rg -n 'theorem integral_eq_sub_of_hasDerivAt\b|theorem integral_const_mul|theorem integral_add ' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/*.lean`
- `python3 -I: lean_name scan of dag.json and nodes/*/decomposition-v*.json; git log --all --oneline -S 'iwl_cr_rh_'; grep iwl_cr_rh_ dag.json issue-workers.json GMT/Ch06/Submission.lean`
- `python3 -I /tmp/rh-decomp/scripts/gen.py (verifier gmt-compare.py child_modules in contract mode + lean_contract.validate_lean_statement); lake env lean /tmp/rh-decomp/gen/*__NodeChallenge.lean /tmp/rh-decomp/gen/*__SolutionEmu.lean`
- `lake env lean /tmp/rh-decomp/Elab1.lean, Elab2.lean, Assembly.lean, ChildA.lean, ChildB.lean, ChildC.lean, Full.lean (#print axioms)`
- `WebSearch: Poincaré lemma star-shaped homotopy operator identity ω = I dω + d I ω`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-homotopy-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-scope-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/rh-decomp/scripts/gen.py`
- `/tmp/rh-decomp/Assembly.lean`
- `/tmp/rh-decomp/ChildA.lean`
- `/tmp/rh-decomp/ChildB.lean`
- `/tmp/rh-decomp/ChildC.lean`
- `/tmp/rh-decomp/Full.lean`

**Snapshot.** Project d8d46c95, Mathlib 25730c7c. Its Ch06 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 ea3ee0dd…).

**Definitions used by the statements.**
- SimonGMT Chapter06/Forms.lean: Covector E n := E [⋀^Fin n]→L[ℝ] ℝ and DifferentialForm E n := E → Covector E n.
- Mathlib DifferentialForm/Basic.lean:72: extDeriv ω x := alternatizeUncurryFin (fderiv ℝ ω x), defined for every ω.

**Library inputs.**
- Normed Alternating/Uncurry/Fin.lean: alternatizeUncurryFin_apply (:137), with a ℤ-power coefficient (-1)^i • …, and alternatizeUncurryFin_curryLeft (:154).
- Normed Alternating/Curry.lean:57: curryLeft_apply_apply, stated with Matrix.vecCons, which equals Fin.cons by rfl (checked in Lean).
- Data/Fin/Tuple/Basic.lean:882: Fin.cons_comp_succ_succAbove; also Fin.removeNth_zero and Fin.tail_cons.
- IntervalIntegral/FundThmCalculus.lean:1148: integral_eq_sub_of_hasDerivAt.
- IntervalIntegral/Basic.lean: integral_add (:774), integral_finsetSum (:778; integral_finset_sum is deprecated) and integral_const_mul (:817).
- hasDerivAt_pow (derivative ↑n * x^(n-1)) and ContDiff.continuous_fderiv.
- Topology/Algebra/Module/Alternating/Topology.lean: ContinuousAlternatingMap.apply (:294, evaluation as a continuous linear map) and the ContinuousEvalConst instance (:189).

**No-match results.**
- No radial homotopy formula or Poincaré lemma for k-forms exists in the snapshot Mathlib. CurveIntegral/Poincare.lean covers only 1-forms via curve integrals on convex sets and does not apply.
- No such formula exists in the project or the SimonGMT package (rg found only unrelated 'radial' files in Chapters 04, 05 and 08).
- The names iwl_cr_rh_integrand_identity, iwl_cr_rh_radial_ftc and iwl_cr_rh_degree_zero are unused in dag.json, the decomposition files, Submission.lean and all git refs.

**Lean checks (lake env lean, contract scope after import GMT.Ch06.Submission).**
- The three child types pass validate_lean_statement and elaborate as the comparator's generated NodeChallenge modules.
- An assembly proves the frozen parent type from the three children.
- Scratch proofs of all children together with the assembled parent compile with no sorry. #print axioms shows [propext, Classical.choice, Quot.sound].
- Emulated NodeSolution checks (exact Submission.X) pass.

**Public citation.** Wikipedia, 'Poincaré lemma' (https://en.wikipedia.org/wiki/Poincar%C3%A9_lemma), states the homotopy formula h_1^* − h_0^* = dJ + Jd, here for the homotopy f_t(x) = tx. For background, see also the standard star-shaped Poincaré lemma in Spivak, Calculus on Manifolds, Thm 4-11. The children's proofs are self-contained direct computations extracted from the supplied parent proof.
