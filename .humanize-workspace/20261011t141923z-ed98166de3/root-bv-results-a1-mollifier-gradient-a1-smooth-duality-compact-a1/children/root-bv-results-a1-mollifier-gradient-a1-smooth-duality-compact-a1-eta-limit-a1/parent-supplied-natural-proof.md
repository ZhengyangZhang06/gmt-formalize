# Parent-supplied natural-language proof

- Parent DAG node: `root.bv_results-a1.mollifier_gradient-a1.smooth_duality_compact-a1`
- Child DAG node: `root.bv_results-a1.mollifier_gradient-a1.smooth_duality_compact-a1.eta_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the selected node's supplied proof, steps 0 and 4–8, applied to the nonnegative continuous function f (in the selected node f = ‖Dw(·)‖) from the already-integrated regularized bound. μ denotes Lebesgue measure (volume) on ℝⁿ and μ(L) := (volume L).toReal.
0. Infinite M. If M = ∞ the conclusion holds trivially (le_top). Otherwise let m := M.toReal. Then m ≥ 0 and M = ofReal m (ENNReal.ofReal_toReal).
1. Preliminaries. L is compact, hence closed, hence measurable, and volume(L) < ∞ (IsCompact.measure_lt_top). So μ(L) ≥ 0 is the finite real measure of L. f is continuous, hence integrable on the compact set L (ContinuousOn.integrableOn_compact), and so is every constant function.
2. The function φ_η. Fix η > 0 and put φ_η(x) := χ(x) f(x)² / √(f(x)² + η²).
 - The denominator is positive because f(x)² + η² ≥ η² > 0 (Real.sqrt_pos).
 - φ_η is continuous: it is built from continuous functions by products, sums, the square root and division by a nonvanishing continuous function.
 - φ_η = χ · (f²/√(f² + η²)), so φ_η has compact support because χ does (HasCompactSupport.mul_right).
 - Being continuous with compact support, φ_η is integrable on ℝⁿ (Continuous.integrable_of_hasCompactSupport).
 - φ_η ≥ 0 everywhere, since χ ≥ 0, f² ≥ 0 and the denominator is positive.
3. Real bound on ∫φ_η. By hypothesis ofReal(∫φ_η) ≤ M = ofReal m. Since m ≥ 0, ENNReal.ofReal_le_ofReal_iff gives ∫φ_η ≤ m.
4. Elementary inequality: for real t ≥ 0 and η > 0, t − η ≤ t²/√(t² + η²).
 - Let s := √(t² + η²) > 0, so s² = t² + η².
 - Since t + η ≥ 0 and (t + η)² = t² + 2tη + η² ≥ t² + η² = s², we get s ≤ t + η (Real.sqrt_le_left).
 - Because s > 0 it suffices to show (t − η)s ≤ t² (le_div_iff₀).
 - If t ≤ η, then (t − η)s ≤ 0 ≤ t².
 - If t > η, then t − η > 0 and (t − η)s ≤ (t − η)(t + η) = t² − η² ≤ t².
5. Pointwise lower bound on L. For x ∈ L, χ(x) = 1, so φ_η(x) = f(x)²/√(f(x)² + η²) ≥ f(x) − η by step 4 with t = f(x) ≥ 0.
6. Integral bound for fixed η.
 - By integral_sub and the set integral of a constant (setIntegral_const), ∫_L f = ∫_L (f − η) + η·μ(L); here f − η is integrable on L by step 1.
 - f − η and φ_η are integrable on the measurable set L, so step 5 and monotonicity of the set integral (setIntegral_mono_on) give ∫_L (f − η) ≤ ∫_L φ_η.
 - φ_η is integrable and nonnegative on ℝⁿ, so ∫_L φ_η ≤ ∫_{ℝⁿ} φ_η (setIntegral_le_integral).
 - Combined with step 3: ∫_L f ≤ m + η·μ(L).
7. Letting η → 0. Let ε > 0 and η := ε/(μ(L) + 1) > 0. Then η·μ(L) = ε·μ(L)/(μ(L) + 1) ≤ ε, so step 6 gives ∫_L f ≤ m + ε. Since ε > 0 is arbitrary, ∫_L f ≤ m (le_of_forall_pos_le_add).
8. Conversion to the lower integral. f is integrable on L and f ≥ 0, so ∫⁻_L ofReal(f(x)) dx = ofReal(∫_L f) (ofReal_integral_eq_lintegral_ofReal for volume restricted to L). By step 7 and monotonicity of ofReal (ENNReal.ofReal_le_ofReal), ∫⁻_L ofReal(f) ≤ ofReal m = M. ∎

## Key steps

1. M = ∞ is trivial; otherwise M = ofReal m with m = M.toReal ≥ 0.
2. For η > 0, φ_η = χf²/√(f²+η²) is continuous, nonnegative and compactly supported, hence integrable, and the hypothesis gives ∫φ_η ≤ m.
3. t − η ≤ t²/√(t²+η²) for t ≥ 0, so φ_η ≥ f − η on L, where χ = 1.
4. ∫_L f = ∫_L (f−η) + ημ(L) ≤ ∫_L φ_η + ημ(L) ≤ ∫φ_η + ημ(L) ≤ m + ημ(L).
5. Let η → 0 (η = ε/(μ(L)+1)) to get ∫_L f ≤ m, then convert with ofReal_integral_eq_lintegral_ofReal.

## Reference use

### local-project

Queries:
- `cmp local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean <workspace>/GMT/Ch02/Contract.lean; cat local-references/ff09f3909baeeae7/manifest.json`
- `rg -n "^theorem (ContDiff\.sqrt|ContDiff\.inner|ContDiff\.norm_sq|ContDiff\.fderiv_right|ContDiff\.clm_apply|ContDiff\.continuous_fderiv)\b" mathlib/Mathlib`
- `rg -n "theorem (sum_repr'|toDual_symm_apply|inner_single_left)\b|def basisFun\b|^theorem sum_inner\b|theorem real_inner_smul_left\b|theorem real_inner_self_eq_norm_sq\b|theorem abs_real_inner_le_norm\b" mathlib/Mathlib/Analysis/InnerProductSpace; rg -n "theorem sum_repr'" mathlib/Mathlib/Analysis/InnerProductSpace/; rg -n "theorem toDual_symm_apply|def toDual\b" mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `rg -n "theorem (opNorm_le_bound|le_opNorm)\b" mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `rg -n "theorem (ofReal_integral_eq_lintegral_ofReal|ofReal_integral_norm_eq_lintegral_enorm|setIntegral_mono_on|setIntegral_le_integral|setIntegral_const|integral_neg|integral_sub)\b" mathlib/Mathlib/MeasureTheory; rg -n "theorem (Continuous\.integrable_of_hasCompactSupport|ContinuousOn\.integrableOn_compact)\b" mathlib/Mathlib`
- `rg -n "theorem (le_of_forall_pos_le_add|ofReal_norm_eq_enorm|ofReal_norm)\b|alias ofReal_norm_eq_enorm|deprecated.*ofReal_norm" mathlib/Mathlib; rg -n "HasCompactSupport.mono|HasCompactSupport.mul_right" mathlib/Mathlib/Topology/Algebra/Support.lean; rg -n measure_lt_top mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean | grep IsCompact`
- `rg -n "^def gradient" mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean; lean checks/Unavail.lean (#check @gradient, @ofReal_norm, @OrthonormalBasis.sum_repr', @le_of_forall_pos_le_add after import GMT.Ch02.Submission)`
- `lean checks/Avail.lean (#check of every cited lemma after import GMT.Ch02.Submission in the contract scope)`
- `python3 -I scripts/gen_checks.py children.json checks/gen GMT/Ch02/Contract.lean (verifier gmt-compare.py child_modules + lean_contract.validate_lean_statement); lean checks/gen/NodeChallenge_00..02.lean`
- `lean checks/Assembly.lean, checks/ProveA.lean, checks/ProveB.lean, checks/ProveC.lean, checks/Combined.lean with #print axioms`
- `lake build GMT.Ch02.Submission on a candidate with the 3 children + assembly inserted before main_theorem; lean checks/gen/NodeSolution_00..03.lean with #print axioms HumanizeNodeComparator.target`
- `scan of lean_name/lean_statement in dag.json and nodes/*/decomposition-v*.json; git grep of the 3 names over all 250 refs (*.lean); grep of the 3 names over .humanize/`
- `grep check_source_delta / check_parent_git_delta / _overlay_accepted_children in /runtime/flows/gmt-claude-4f40c99d0e11/_recursive_lean/{leaf_verification,parent_verification,runtime}.py`
- `grep -n "2.5 Lemma" book/sources/chapter-02-source.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-4f40c99d0e11/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-4f40c99d0e11/_recursive_lean/parent_verification.py`
- `/runtime/flows/gmt-claude-4f40c99d0e11/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-mollifier-gradient-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-mollifier-gradient-a1-smooth-duality-compact-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/tmp/sdc-decomp-RgRO9S/checks/Avail.lean`
- `/tmp/sdc-decomp-RgRO9S/checks/Unavail.lean`
- `/tmp/sdc-decomp-RgRO9S/checks/gen/NodeChallenge_00.lean`
- `/tmp/sdc-decomp-RgRO9S/checks/gen/NodeChallenge_01.lean`
- `/tmp/sdc-decomp-RgRO9S/checks/gen/NodeChallenge_02.lean`
- `/tmp/sdc-decomp-RgRO9S/checks/Assembly.lean`
- `/tmp/sdc-decomp-RgRO9S/checks/ProveA.lean`
- `/tmp/sdc-decomp-RgRO9S/checks/ProveB.lean`
- `/tmp/sdc-decomp-RgRO9S/checks/ProveC.lean`
- `/tmp/sdc-decomp-RgRO9S/checks/Combined.lean`
- `/tmp/sdc-cand-dtjVU9/GMT/Ch02/Submission.lean`
- `/tmp/sdc-cand-dtjVU9/checks/gen/NodeSolution_00.lean`
- `/tmp/sdc-cand-dtjVU9/checks/gen/NodeSolution_01.lean`
- `/tmp/sdc-cand-dtjVU9/checks/gen/NodeSolution_02.lean`
- `/tmp/sdc-cand-dtjVU9/checks/gen/NodeSolution_03.lean`

The snapshot (project 1b1689a8, Mathlib 25730c7c) Contract.lean is byte-identical to the workspace contract.
Every tool the children cite is in the snapshot and is a known constant after import GMT.Ch02.Submission (#check):
- calculus: ContDiff.fderiv_right (Calculus/ContDiff/Comp.lean:750), ContDiff.clm_apply (Comp.lean:495), ContDiff.continuous_fderiv (ContDiff/Defs.lean:1271), ContDiff.sqrt (SpecialFunctions/Sqrt.lean:164), ContDiff.inner and ContDiff.norm_sq (InnerProductSpace/Calculus.lean:81,144);
- inner products: EuclideanSpace.basisFun and OrthonormalBasis.sum_repr' (PiL2.lean:802,499), real_inner_smul_left, sum_inner, real_inner_self_eq_norm_sq and abs_real_inner_le_norm (InnerProductSpace/Basic.lean:110,159,398,471), InnerProductSpace.toDual and toDual_symm_apply (Dual.lean:136,178);
- operator norm: ContinuousLinearMap.opNorm_le_bound and le_opNorm (Normed/Operator/Basic.lean:196,234);
- integration: integral_neg, integral_sub and ofReal_integral_eq_lintegral_ofReal (Integral/Bochner/Basic.lean:256,263,739), setIntegral_const, setIntegral_le_integral and setIntegral_mono_on (Bochner/Set.lean:524,742,761), ContinuousOn.integrableOn_compact and Continuous.integrable_of_hasCompactSupport (Function/LocallyIntegrable.lean:592,622), IsCompact.measure_lt_top (Measure/Typeclasses/Finite.lean:346);
- supports and norms: HasCompactSupport.mul_right (Topology/Algebra/Support.lean:477) and ofReal_norm (ofReal_norm_eq_enorm is a deprecated alias at Normed/Group/Basic.lean:389).
HasCompactSupport.mono and the root le_of_forall_pos_le_add are to_additive-generated; #check confirms both. rg finds only the ENNReal version of the latter, at Basic/ENNReal/Basic.lean:613.
No-match and unavailable results:
- Mathlib's gradient (Calculus/Gradient/Basic.lean:83) is an unknown identifier after import GMT.Ch02.Submission, so riesz_gradient builds G from basisFun;
- no DAG node or decomposition subproblem states an equivalent gradient, regularized-field or η-limit lemma (the nearest, smoothed_abs, is a different statement);
- the 3 proposed names occur in no dag.json node, no nodes/*/decomposition file and no *.lean file of the 250 git refs.
Lean evidence:
- NodeChallenge files from the verifier's child_modules compile for all 3 statements;
- ProveA/B/C prove them outright with axioms propext, Classical.choice and Quot.sound;
- Assembly.lean and the candidate-Submission NodeSolution for the selected node prove its exact frozen type, byte-identical to dag.json, from the 3 children plus the bv_exists_smooth_cutoff stub (sorryAx only from that stub);
- the combined single-theorem proof also compiles under the default heartbeat limit.
Workflow constraints: a leaf may append exactly one theorem without helpers or set_option (leaf_verification.check_source_delta), and a node's worktree overlays only node.children and node.depends_on (runtime._overlay_accepted_children). So the cut-off stays with the selected node, and the children are self-contained.
Book: Simon Lemma 2.5, identity (4) (chapter-02-source.txt) is the smooth duality this node proves on compact sets.
