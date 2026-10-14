# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.mollified_uniform-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.mollified_uniform-a1.conv_lipschitz-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1 and 3 (regularity of φ; equi-Lipschitz estimate) of the selected theorem's supplied proof, stated for an arbitrary set S and an arbitrary integrable v (the parent uses S = B_{2R}(0), v = u_k). All integrals are with respect to Lebesgue measure (volume) on ℝⁿ = Euclid n; ∫_S denotes the integral for volume restricted to S (S need not be measurable).
1. (φ is Lipschitz.) φ is C^∞, hence C¹ (the smoothness order ⊤ is ≠ 0), and has compact support, so φ is globally Lipschitz. There is C ∈ ℝ≥0 with |φ(z) − φ(z')| = dist(φ(z), φ(z')) ≤ C·dist(z, z') for all z, z' ∈ ℝⁿ (ContDiff.lipschitzWith_of_hasCompactSupport with the side condition ⊤ ≠ 0 closed by simp, then LipschitzWith.dist_le_mul and Real.dist_eq). Set L := C (as a real number); then L ≥ 0. L is chosen here, before S, v, x, x', so it depends only on φ.
2. (φ is bounded.) φ is continuous (ContDiff.continuous) with compact support, so there is M ∈ ℝ with |φ(z)| ≤ M for all z (Continuous.bounded_above_of_compact_support).
3. (Integrability.) Fix S, v integrable on S, and x, x' ∈ ℝⁿ. For any z ∈ ℝⁿ, the map y ↦ φ(z − y) is continuous (φ composed with the continuous map y ↦ z − y). Hence it is AE-strongly measurable for volume restricted to S, and it is bounded by M everywhere. Therefore y ↦ v(y)·φ(z − y) is integrable on S (Integrable.mul_bdd: integrable times bounded AE-strongly measurable). Apply this with z = x and with z = x'.
4. (Linearity.) By step 3 and integral_sub, ∫_S v(y)φ(x − y) dy − ∫_S v(y)φ(x' − y) dy = ∫_S g(y) dy, where g(y) := v(y)φ(x − y) − v(y)φ(x' − y).
5. (Pointwise bound.) For every y, g(y) = v(y)·(φ(x − y) − φ(x' − y)) (mul_sub), so |g(y)| = |v(y)|·|φ(x − y) − φ(x' − y)| (abs_mul). By step 1 and translation invariance of the distance, dist(x − y, x' − y) = dist(x, x') (dist_sub_right). So |φ(x − y) − φ(x' − y)| ≤ C·dist(x, x'), and since |v(y)| ≥ 0, |g(y)| ≤ |v(y)|·(C·dist(x, x')).
6. (Integral bound.) First, |∫_S g| ≤ ∫_S |g| (abs_integral_le_integral_abs). The function y ↦ |v(y)|·(C·dist(x, x')) is integrable on S (|v| is integrable on S by Integrable.abs; multiply by a constant with Integrable.mul_const), and |g| ≥ 0 everywhere. So integral_mono_of_nonneg together with step 5 gives ∫_S |g| ≤ ∫_S |v(y)|·(C·dist(x, x')) dy = (∫_S |v|)·C·dist(x, x') (integral_mul_const).
7. (Conclusion.) By steps 4 and 6, |∫_S v(y)φ(x − y) dy − ∫_S v(y)φ(x' − y) dy| ≤ C·(∫_S |v|)·dist(x, x') = L·(∫_S |v|)·dist(x, x'), with L = C ≥ 0 independent of S, v, x, x'. ∎

## Key steps

1. φ is Lipschitz with some constant C ≥ 0 (C¹ with compact support) and bounded by some M (continuous with compact support); take L := C.
2. For every z, y ↦ v(y)φ(z − y) is integrable on S (integrable times bounded continuous; Integrable.mul_bdd).
3. The difference of the two integrals equals ∫_S v(y)(φ(x − y) − φ(x' − y)) dy (integral_sub).
4. Pointwise |v(y)||φ(x − y) − φ(x' − y)| ≤ |v(y)|·C·dist(x, x') by the Lipschitz bound and dist(x − y, x' − y) = dist(x, x').
5. |∫ g| ≤ ∫|g| ≤ ∫_S |v|·C·dist(x, x') = C(∫_S|v|)dist(x, x') (abs_integral_le_integral_abs, integral_mono_of_nonneg, integral_mul_const).

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
