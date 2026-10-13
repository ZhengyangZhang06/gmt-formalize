# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.rescaled_bounds-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.rescaled_bounds-a1.null_seq_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the limit arguments of steps 5 and 7 of the parent proof (composition with λ_iR → 0 in 𝓝[>] 0, and multiplication by the finite constant V(R)), stated for an arbitrary positive null sequence s and an arbitrary finite constant C.
1. (s tends to 0 from the right.) Since s_i → 0 and s_i ∈ (0, ∞) for every i, s tends to 0 within (0, ∞), i.e. s → 0 along 𝓝[>] 0 (tendsto_nhdsWithin_iff). Consequently, if a property Q(r) holds for all r in some member of 𝓝[>] 0, then Q(s_i) holds for all sufficiently large i.
2. (Pulling out the constant in (i).) Assume limsup_{r→0⁺} f(r) ≤ 1. Since C ≠ ∞, limsup_i C·f(s_i) = C·limsup_i f(s_i) (ENNReal.limsup_const_mul_of_ne_top, valid for every filter; ENNReal.limsup_const_mul would instead require a countable-intersection filter). Hence it suffices to show L := limsup_i f(s_i) ≤ 1, because then limsup_i C·f(s_i) = C·L ≤ C·1 = C (monotonicity of multiplication in [0,∞]).
3. (L ≤ 1.) Let c ∈ [0,∞] with c > 1. Then limsup_{r→0⁺} f(r) ≤ 1 < c, so f(r) < c for all r in some member of 𝓝[>] 0 (eventually_lt_of_limsup_lt; its boundedness side condition holds automatically in the complete lattice [0,∞]). By step 1, f(s_i) < c, hence f(s_i) ≤ c, for all sufficiently large i, and therefore L ≤ c (limsup_le_of_le). Since this holds for every c > 1 and [0,∞] is densely ordered, L ≤ 1 (le_of_forall_gt_imp_ge_of_dense). This proves (i).
4. (Part (ii).) Assume h(r) → 0 along 𝓝[>] 0. Composing with step 1 gives h(s_i) → 0 as i → ∞ (Tendsto.comp). Since C ≠ ∞, multiplication by the constant C preserves this limit in [0,∞] (ENNReal.Tendsto.const_mul, whose side condition 'limit ≠ 0 or C ≠ ∞' holds because C ≠ ∞), so C·h(s_i) → C·0 = 0. ∎

## Key steps

1. s_i > 0 and s_i → 0 give s → 0 along 𝓝[>] 0 (tendsto_nhdsWithin_iff).
2. C ≠ ∞ ⇒ limsup_i C·f(s_i) = C·limsup_i f(s_i) (ENNReal.limsup_const_mul_of_ne_top).
3. For every c > 1, eventually f(s_i) < c, so limsup_i f(s_i) ≤ c; density of [0,∞] gives limsup_i f(s_i) ≤ 1, hence limsup_i C·f(s_i) ≤ C.
4. h(s_i) → 0 by composition, and C·h(s_i) → C·0 = 0 by ENNReal.Tendsto.const_mul since C ≠ ∞.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Contract.lean and GMT/Ch07/Submission.lean (both identical)`
- `grep -n 'def dilation\|def dilationCLM\|def unitBallVolume' project/GMT/Ch07/Contract.lean (dilation x lam y = -(lam⁻¹ • x) + dilationCLM P lam y, dilationCLM = lam⁻¹ • id, unitBallVolume n = volume (ball (0 : Euclid n) 1)); grep -rn 'def blowUpMap' simongmt Poincare/SimonGMT/Chapter03/Rectifiable.lean (blowUpMap x r y = r⁻¹ • (y - x))`
- `python3 -I scans of dag.json: frozen lean_statement of the parent's prerequisites cbr_ci_bl_blowUp_restrict_scaling and cbr_ci_bl_density_bounds (byte-identical to the stubs used); search for existing dilation/blowUpMap ball lemmas (accepted regcomp_atl_blowUp_measure_scaling / rsdic_tl_blowUp_measure_scaling / ptd_tl_blowUp_measure_scaling cover only closed-ball masses; dtc_rescaled_ball_measure_tendsto concerns density limits; none reused); lean_name collision check for cbr_ci_bl_rb_scale_identities, cbr_ci_bl_rb_null_seq_transfer, cbr_ci_bl_rb_compact_sup_bound (no match)`
- `grep -rn in local-references/123e8435b4a2469b/mathlib/Mathlib: MeasurableEmbedding.lintegral_map, MeasurableEmbedding.restrict_map, map_apply (hf : MeasurableEmbedding f), Measure.restrict_smul, lintegral_smul_measure, Measure.restrict_restrict, Homeomorph.measurableEmbedding, Homeomorph.smulOfNeZero, ENNReal.mul_div_mul_left, ENNReal.ofReal_div_of_pos, measure_ball_pos, measure_ball_lt_top, inv_mul_le_iff₀, inv_mul_lt_iff₀, ENNReal.limsup_const_mul_of_ne_top, eventually_lt_of_limsup_lt, limsup_le_of_le, le_of_forall_gt_imp_ge_of_dense, ENNReal.Tendsto.const_mul, tendsto_nhdsWithin_iff, Bornology.IsBounded.subset_closedBall, ENNReal.sum_lt_top, Finset.single_le_sum, ENNReal.div_le_of_le_mul, ENNReal.le_div_iff_mul_le`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose depth gate: depth 5 < max_depth 6; _solve_children and _existing_lean_name_problem: children depend only on sibling keys, accepted identical-type reuse only) and speculation.py (appended Submission.X theorems inside namespace GMT.Ch07)`
- `lake env lean /tmp/rb-decomp/Stmts.lean, C1.lean, C2.lean, C3.lean, Assembly.lean, EndToEnd.lean with #print axioms; validate_lean_statement from verifier/lean_contract.py and the runtime lean_contract.py on the three child types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6264bc6f37/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6264bc6f37/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/NhdsWithin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/BigOperators.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/speculation.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/rb-decomp/C1.lean`
- `/tmp/rb-decomp/C2.lean`
- `/tmp/rb-decomp/C3.lean`
- `/tmp/rb-decomp/EndToEnd.lean`

The snapshot contract (project b4d606db, Mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean. dilation, dilationCLM, unitBallVolume and blowUpMap have the definitions used in the child proofs. No existing DAG declaration gives the open-ball, total-mass and lintegral scaling identities. The accepted regcomp_atl_blowUp_measure_scaling covers only closed-ball masses, so nothing is reused. The three new cbr_ci_bl_rb_* names are fresh. Every Mathlib lemma cited in the child proofs exists in the pinned snapshot. ENNReal.limsup_const_mul_of_ne_top works for atTop, unlike ENNReal.limsup_const_mul. All three child types elaborate in namespace GMT.Ch07 after import GMT.Ch07.Submission and pass both lexical validators. Each child was fully proved in scratch Lean with only propext, Classical.choice and Quot.sound. The byte-identical frozen parent type was proved from the three children plus the frozen statements of cbr_ci_bl_blowUp_restrict_scaling and cbr_ci_bl_density_bounds, and depends on no other axioms.
