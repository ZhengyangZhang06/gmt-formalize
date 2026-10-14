# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.poincare_sum-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.poincare_sum-a1.ball_volume-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof of fiw_tb_tda_poincare_sum, which places the ball inside the box [−r, r]^n.

Notation.
- E := Eucl n and L := volume on E.
- ofLp : E → (Fin n → ℝ), x ↦ (x_i)_i, is the canonical identification WithLp.ofLp.
- a, b : Fin n → ℝ are the constant functions a_i := −r and b_i := r.
- Icc(a, b) = {z : a_i ≤ z_i ≤ b_i for all i} ⊆ (Fin n → ℝ).

1. (Coordinates are bounded by the norm.) For x ∈ E and i ∈ Fin n, |x_i| ≤ ‖x‖. By EuclideanSpace.norm_eq, ‖x‖ = √(Σ_j |x_j|²) ≥ √(|x_i|²) = |x_i|. Equivalently, use PiLp.norm_apply_le together with ‖x_i‖ = |x_i| (Real.norm_eq_abs).

2. (Ball inside the box.) Let x ∈ closedBall(0, r). Then ‖x‖ = dist(x, 0) ≤ r (dist_zero_right). By step 1, |x_i| ≤ r, i.e. −r ≤ x_i ≤ r (abs_le), for every i. Hence closedBall(0, r) ⊆ ofLp⁻¹(Icc(a, b)).

3. (Volume of the box.)
   - ofLp is measure preserving from (E, L) to (Fin n → ℝ, volume) (PiLp.volume_preserving_ofLp), and Icc(a, b) is measurable (measurableSet_Icc). So L(ofLp⁻¹(Icc(a, b))) = volume(Icc(a, b)).
   - By Real.volume_Icc_pi, volume(Icc(a, b)) = ∏_{i ∈ Fin n} ofReal(b_i − a_i) = ∏_{i ∈ Fin n} ofReal(r − (−r)).
   - By Finset.prod_const and card(Fin n) = n, this equals ofReal(2r)^n.
   - Since r ≥ 0, we have 2r ≥ 0, so ENNReal.ofReal_pow gives ofReal(2r)^n = ofReal((2r)^n).
   For n = 0 the product is empty and both sides equal 1.

4. (Conclusion.) By monotonicity of measures (measure_mono) and steps 2–3, L(closedBall(0, r)) ≤ L(ofLp⁻¹(Icc(a, b))) = ofReal((2r)^n). ∎

## Key steps

1. Each coordinate is bounded by the norm: |x_i| ≤ ‖x‖ in Eucl n (EuclideanSpace.norm_eq, or PiLp.norm_apply_le).
2. closedBall(0, r) ⊆ ofLp⁻¹(Icc(−r, r)^{Fin n}).
3. ofLp preserves volume (PiLp.volume_preserving_ofLp), and Real.volume_Icc_pi gives box volume ∏_i ofReal(2r) = ofReal(2r)^n = ofReal((2r)^n) (ENNReal.ofReal_pow, using r ≥ 0).
4. Monotonicity of measure gives L(closedBall(0, r)) ≤ ofReal((2r)^n).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (identical)`
- `rg -n "theorem lintegral_add_left_eq_self|lintegral_mul_left_eq_self|theorem lintegral_lintegral_swap|theorem volume_preserving_ofLp|theorem volume_Icc_pi\b|theorem lintegral_indicator_const\b|theorem norm_eq \(|theorem setLIntegral_mono'|theorem tsum_mul_left|theorem lintegral_mono_set\b" mathlib/Mathlib`
- `rg -n "volume_preserving_ofLp|theorem volume_closedBall|norm_apply_le|norm_eq" Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean Mathlib/Analysis/InnerProductSpace/PiL2.lean Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `rg -n "theorem mul_le_mul_left'|theorem ofReal_coe_nnreal|theorem coe_nnreal_eq" mathlib/Mathlib (mul_le_mul_left' absent at this revision; ENNReal.ofReal_coe_nnreal present)`
- `rg -n "lintegral_add_left_eq_self|lintegral_lintegral_swap|volume_closedBall|volume \(closedBall" lake-packages-25730c7c/simongmt (SimonGMT)`
- `rg -n "closedBall|lintegral_add_left|Poincar" local-references/.../project/GMT`
- `python3 scan of dag.json (458 nodes): statuses, lean_name collisions, statements mentioning volume (closedBall / x + h, and the frozen sibling fiw_tb_tda_lattice_cubes type`
- `git log --all --oneline -S fiw_tb_tda_ps_ (no match)`
- `grep runtime.py: _overlay_accepted_children, _existing_lean_name_problem, _solve_children, child.proof_base_commit = dispatch commit`
- `verifier/gmt-compare.py contract_scope/child_modules used to generate NodeChallenge/NodeSolution for both children; validate_lean_statement from runtime and verifier lean_contract.py (both pass)`
- `lean (LEAN_PATH from lake env) on /tmp/psum-decomp-17747/{Assembly,ProtoA,ProtoB,Full,Chal_*,Sol_*}.lean: 0 errors`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Group/LIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Poincare.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/EuclideanHausdorffUpper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-poincare-sum-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/psum-decomp-17747/Assembly.lean`
- `/tmp/psum-decomp-17747/ProtoA.lean`
- `/tmp/psum-decomp-17747/ProtoB.lean`
- `/tmp/psum-decomp-17747/Full.lean`

Snapshot: project d8d46c95 with Mathlib 25730c7c. Contract.lean is identical to the workspace's Contract.lean and Submission.lean.

Neither the project nor SimonGMT has the translation-to-ball double-integral estimate or the box bound for ball volume. SimonGMT has only Tonelli uses (Chapter04) and the exact Gamma-function ball volume (Chapter01). No DAG node has either obligation, so they become the two children: fiw_tb_tda_ps_translation_ball and fiw_tb_tda_ps_ball_volume_le. Both names are unused.

Mathlib API found at the pinned revision: lintegral_add_left_eq_self (to_additive of lintegral_mul_left_eq_self), lintegral_lintegral_swap, lintegral_indicator_const, setLIntegral_mono', lintegral_mono_set, ENNReal.tsum_mul_left, PiLp.volume_preserving_ofLp, Real.volume_Icc_pi, PiLp.norm_apply_le, EuclideanSpace.norm_eq and ENNReal.ofReal_coe_nnreal. Exact ball-volume formulas exist (EuclideanSpace.volume_closedBall) but involve Gamma, so the box bound is simpler. mul_le_mul_left' is absent at this revision; use mul_le_mul' or gcongr.

Children of this node cannot use the sibling lattice_cubes, because their proof base is this node's dispatch commit. So steps 1–2, which use it, stay in the parent.

Scratch Lean checks:
- The frozen parent type compiles from stubs of the frozen lattice_cubes type and both child types (5,648 heartbeats; sorryAx only from the lattice_cubes stub).
- Scratch proofs of both children compile, and the comparator-style NodeSolution targets close by `exact Submission.X` with only propext, Classical.choice and Quot.sound.
- Both types pass validate_lean_statement.
