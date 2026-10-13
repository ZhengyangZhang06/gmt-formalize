# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.mollified_uniform-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.mollified_uniform-a1.translate_admissible-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the selected theorem's supplied proof (b_x = φ(x − ·) is an admissible test function in B_{2R}(0) with ∫b_x = ∫φ), together with the compact-support part of its step 1. Notation: ℝⁿ = Euclid n with Lebesgue measure (volume); e(y) := x − y; b := φ ∘ e, i.e. b(y) = φ(x − y).
1. (φ has compact support.) tsupport φ is closed (isClosed_tsupport) and tsupport φ ⊆ ball(0, s) ⊆ closedBall(0, s) (ball_subset_closedBall). closedBall(0, s) is compact because ℝⁿ is a proper space (isCompact_closedBall). A closed subset of a compact set is compact (IsCompact.of_isClosed_subset), so tsupport φ is compact, i.e. HasCompactSupport φ.
2. (e is a smooth homeomorphism.) e(y) = x − y is a homeomorphism of ℝⁿ (it is its own inverse; in Mathlib it is Homeomorph.subLeft x, and (fun y => φ (x − y)) = φ ∘ Homeomorph.subLeft x holds by rfl). It is C^∞, being the difference of the constant map y ↦ x and the identity (contDiff_const.sub contDiff_id).
3. (b is smooth.) b = φ ∘ e is a composition of C^∞ maps, hence ContDiff ℝ ⊤ (ContDiff.comp: hφ.comp (contDiff_const.sub contDiff_id)).
4. (b has compact support.) Precomposition with a homeomorphism preserves compact support: from step 1 and HasCompactSupport.comp_homeomorph we get HasCompactSupport (φ ∘ e). (Concretely, tsupport(φ ∘ e) = e⁻¹(tsupport φ) = e(tsupport φ) because e = e⁻¹; this is a continuous image of a compact set.)
5. (Support inclusion.) For a homeomorphism e, tsupport(φ ∘ e) = e⁻¹(tsupport φ) (tsupport_comp_eq_preimage). Let y ∈ tsupport b. Then x − y = e(y) ∈ tsupport φ ⊆ ball(0, s), so ‖x − y‖ < s (mem_ball_zero_iff); and x ∈ closedBall(0, R) means ‖x‖ ≤ R (mem_closedBall_zero_iff). Since y = x − (x − y), the triangle inequality (norm_sub_le) gives ‖y‖ ≤ ‖x‖ + ‖x − y‖ < R + s < R + R = 2R, using s < R. Hence y ∈ ball(0, 2R), so tsupport b ⊆ ball(0, 2R).
6. (Integral.) Lebesgue measure on Euclid n is an additive Haar measure, invariant under translations and under negation y ↦ −y. Hence the change of variables y ↦ x − y preserves it and ∫ φ(x − y) dy = ∫ φ(y) dy (integral_sub_left_eq_self φ volume x). This identity is a change of variables by a measure-preserving equivalence and needs no integrability hypothesis.
7. Steps 3, 4, 5 and 6 are exactly the four conjuncts of the conclusion. (No positivity of s or R is used: if s ≤ 0 then ball(0, s) = ∅, φ vanishes identically, and the same argument applies verbatim.) ∎

## Key steps

1. tsupport φ is a closed subset of the compact closedBall(0, s), so φ has compact support.
2. b = φ ∘ e with e(y) = x − y a smooth self-inverse homeomorphism (Homeomorph.subLeft x), so b is C^∞ and has compact support (HasCompactSupport.comp_homeomorph).
3. tsupport b = e⁻¹(tsupport φ); for such y, ‖y‖ ≤ ‖x‖ + ‖x − y‖ < R + s < 2R, so tsupport b ⊆ ball(0, 2R).
4. ∫ φ(x − y) dy = ∫ φ by invariance of Lebesgue (additive Haar) measure under y ↦ x − y (integral_sub_left_eq_self).

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `rg -n 'theorem .*tendstoUniformlyOn.*equicontinu|theorem .*Equicontinu.*tendsto_uniformOnFun' <snapshot>/mathlib/Mathlib (only Topology/UniformSpace/Ascoli.lean:167,333,361: whole-family equicontinuity, UniformOnFun form; no 'eventually equi-Lipschitz + pointwise => TendstoUniformlyOn' lemma)`
- `rg -n in <snapshot>/mathlib/Mathlib: tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (Topology/UniformSpace/LocallyUniformConvergence.lean:144); tendstoUniformlyOn_iff / tendstoLocallyUniformlyOn_iff (Topology/MetricSpace/Pseudo/Basic.lean:142,132); finite_cover_balls_of_compact + alias IsCompact.finite_cover_balls (Topology/MetricSpace/Pseudo/Basic.lean:255,260); eventually_all_finite + alias Set.Finite.eventually_all (Order/Filter/Finite.lean:252,256)`
- `rg -n in <snapshot>/mathlib/Mathlib: ContDiff.lipschitzWith_of_hasCompactSupport (Analysis/Calculus/ContDiff/RCLike.lean:156); Continuous.bounded_above_of_compact_support (Analysis/Normed/Group/Bounded.lean:153); Integrable.mul_bdd (MeasureTheory/Function/L1Space/Integrable.lean:1072); abs_integral_le_integral_abs (MeasureTheory/Integral/Bochner/Basic.lean:982); integral_mono_of_nonneg (Bochner/Basic.lean:676); integral_sub (Bochner/Basic.lean:263); integral_mul_const (Bochner/Basic.lean:294)`
- `rg -n in <snapshot>/mathlib/Mathlib: integral_div_left_eq_self [to_additive integral_sub_left_eq_self] (MeasureTheory/Group/Integral.lean:163); mulTSupport_comp_eq_preimage [to_additive tsupport_comp_eq_preimage] (Topology/Algebra/Support.lean:106); HasCompactMulSupport.comp_homeomorph (Topology/Algebra/Support.lean:562); Homeomorph.divLeft [to_additive subLeft] (Topology/Algebra/Group/ContinuousDiv.lean:72); dist_div_right [to_additive dist_sub_right] (Topology/MetricSpace/IsometricSMul.lean:282)`
- `python3 -I scans of runs/20261011T150044Z-ba604216b4/dag.json: selected node record (depth 5, frozen lean_statement), sibling frozen types (bv_estimate, l1_constant, top_density), lean_name prefix cbr_ci_pw_mu_ (no match among 1541 names), statements containing TendstoUniformlyOn / Lipschitz / mollify / translate (accepted cmcs_ls_mollify_lipschitz, codim1_rdo_dg_bvc_mollified_lipschitz, codim1_rdo_dg_bvc_translate_test_le, adr_weak_tendsto_of_tendstoUniformly, dorwbl_diff_quotient_tendstoUniformlyOn: different types, not reusable)`
- `git log --all --oneline -S 'cbr_ci_pw_mu_' (no commits); git show 16144a475b (accepted Submission.X theorems are inserted in namespace GMT.Ch07 before main_theorem)`
- `lake env lean /tmp/mu-decomp-7c1e/Types.lean (three child types elaborate after import GMT.Ch07.Submission with the contract's opens; selected frozen type proved from them; only the three child sorry warnings)`
- `lake env lean /tmp/mu-decomp-7c1e/Proofs.lean and /tmp/mu-decomp-7c1e/Full.lean (complete trial proofs of all three children plus the parent assembly: no errors or warnings; #print axioms = [propext, Classical.choice, Quot.sound] for all four declarations)`
- `python3 -I validate_lean_statement from verifier/lean_contract.py on the four types (all pass); byte comparison of the tested parent type with the DAG frozen type (True)`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/prompts.py (DECOMPOSE, DECOMPOSITION_AUDIT), runtime.py _decompose (depth 5 < max_depth, so a split is allowed), leaf_verification.py check_source_delta (one appended theorem, no helper declarations)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-03314b82bb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-03314b82bb/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-03314b82bb/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/Ascoli.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/LocallyUniformConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Group/ContinuousDiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/IsometricSMul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/prompts.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/tmp/mu-decomp-7c1e/Types.lean`
- `/tmp/mu-decomp-7c1e/Proofs.lean`
- `/tmp/mu-decomp-7c1e/Full.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c). The snapshot Mathlib has no lemma that directly turns pointwise convergence plus an eventual equi-Lipschitz bound into TendstoUniformlyOn: Ascoli's EquicontinuousOn.tendsto_uniformOnFun_iff_pi requires the whole family to be equicontinuous and is phrased with UniformOnFun. So the ε/3 lemma is a genuine child. Every Mathlib lemma cited in the child proofs exists at the listed location and was exercised in a compiled trial proof. No DAG node or comparator-accepted declaration has any of the three child types, and the cbr_ci_pw_mu_ names are fresh in the DAG and in git history. All three child types elaborate in the contract scope; the selected frozen type (byte-identical to the DAG) is proved from them, and complete trial proofs of the children compile with only the standard axioms.
