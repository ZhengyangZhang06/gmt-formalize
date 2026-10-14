# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.mollified_uniform-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.mollified_uniform-a1.uniform_of_equilipschitz-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 (uniformity) of the selected theorem's supplied proof, abstracted from w_k to an arbitrary sequence F_k with a constant pointwise limit a. This is the standard ε/3 argument: pointwise convergence plus equicontinuity on a compact set gives uniform convergence.
1. (Reduction to an ε-statement.) By Metric.tendstoUniformlyOn_iff, TendstoUniformlyOn F (fun _ => a) atTop K holds iff for every ε > 0, for all sufficiently large k, dist(a, F_k(x)) < ε for every x ∈ K. On ℝ, dist(p, q) = |p − q| (Real.dist_eq). So fix ε > 0; we must show ∀ᶠ k in atTop, ∀ x ∈ K, |a − F_k(x)| < ε.
2. (Choice of the mesh.) Put L⁺ := max(L, 0), so L⁺ ≥ 0 and L ≤ L⁺, and put η := ε/(3(L⁺ + 1)). Then η > 0, and L⁺·η = (ε/3)·L⁺/(L⁺ + 1) < ε/3 because 0 ≤ L⁺ < L⁺ + 1 and ε > 0 (cross-multiplied: 3·L⁺·ε < 3·(L⁺ + 1)·ε).
3. (Finite η-net.) K is compact, so finite_cover_balls_of_compact (alias IsCompact.finite_cover_balls) with radius η > 0 gives a finite set t ⊆ K with K ⊆ ⋃_{z ∈ t} ball(z, η).
4. (Pointwise convergence on the net.) For each z ∈ t we have z ∈ K, so by (i) F_k(z) → a. By Metric.tendsto_nhds with ε/3 > 0, eventually dist(F_k(z), a) = |F_k(z) − a| < ε/3. Because t is finite, these finitely many eventual statements hold simultaneously (Set.Finite.eventually_all, i.e. Filter.eventually_all_finite): ∀ᶠ k in atTop, ∀ z ∈ t, |F_k(z) − a| < ε/3.
5. (Intersect with the Lipschitz hypothesis.) Hypothesis (ii) is also an eventual statement in k, and two eventual statements hold together eventually (filter_upwards). Fix any k for which both the conclusion of step 4 and the inequality of (ii) hold, and fix x ∈ K.
6. (Nearby centre.) By step 3, x ∈ ball(z, η) for some z ∈ t, i.e. dist(x, z) < η, hence dist(z, x) < η (dist_comm). Since z ∈ t ⊆ K and x ∈ K, (ii) gives |F_k(z) − F_k(x)| ≤ L·dist(z, x) ≤ L⁺·dist(z, x) ≤ L⁺·η < ε/3. The second inequality uses dist(z, x) ≥ 0 and L ≤ L⁺; the third uses L⁺ ≥ 0 and dist(z, x) < η; the last is step 2.
7. (Triangle inequality.) |a − F_k(x)| = |(a − F_k(z)) + (F_k(z) − F_k(x))| ≤ |a − F_k(z)| + |F_k(z) − F_k(x)| = |F_k(z) − a| + |F_k(z) − F_k(x)| < ε/3 + ε/3 < ε, by step 4 (z ∈ t) and step 6.
8. (Conclusion.) Steps 5–7 show ∀ᶠ k in atTop, ∀ x ∈ K, dist(a, F_k(x)) < ε. Since ε > 0 was arbitrary, step 1 gives TendstoUniformlyOn F (fun _ => a) atTop K. If K = ∅, the conclusion of step 5 holds vacuously, so no case split is needed. ∎
Formalization note (optional alternative with the same mathematics): instead of the global net one may use tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (K compact) together with Metric.tendstoLocallyUniformlyOn_iff. For x ∈ K take the neighbourhood K ∩ ball(x, η) ∈ 𝓝[K] x, and apply the estimate of steps 6–7 with the centre z := x.

## Key steps

1. Reduce to: for every ε > 0, eventually ∀ x ∈ K, |a − F_k(x)| < ε (Metric.tendstoUniformlyOn_iff).
2. Choose η = ε/(3(max(L,0)+1)), so max(L,0)·η < ε/3.
3. Cover the compact K by finitely many η-balls with centres in a finite t ⊆ K (finite_cover_balls_of_compact).
4. Eventually every centre z ∈ t satisfies |F_k(z) − a| < ε/3 (finitely many eventualities), and eventually the Lipschitz bound (ii) holds.
5. For x ∈ K pick z ∈ t with dist(z, x) < η; then |F_k(z) − F_k(x)| < ε/3 and the triangle inequality gives |a − F_k(x)| < ε.

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
