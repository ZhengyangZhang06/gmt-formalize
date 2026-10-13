# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.series_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, proof of Theorem 7.2, the M-absolutely convergent series R^(ℓ) = Σ_{r≥ℓ} R_r, S^(ℓ) = Σ_{r≥ℓ} S_r (step 6 of the parent proof: "the series converge absolutely since |R_r(ω)| ≤ |ω|_∞ M(R_r) … they define currents"). Admissible below means admissible for M_U: ω ∈ 𝒟ⁿ(U) with |ω(x)| ≤ 1 for all x (tsupport ω ⊆ U holds automatically).
1. (The norm |·|.) For an n-covector α, |α| = (Σ_I α(e_{I_1}, …, e_{I_n})²)^{1/2}, the sum over strictly increasing I : {1, …, n} → {1, …, P}. Each α ↦ α(e_{I_1}, …, e_{I_n}) is a continuous linear map, so |·| is continuous; |tα| = |t|·|α| for t ∈ ℝ, because (Σ_I (tα(e_I))²)^{1/2} = (t²·Σ_I α(e_I)²)^{1/2} = |t|·(Σ_I α(e_I)²)^{1/2} (a direct consequence of the definition; SimonGMT only records the cases t = 0 and t = −1); and |α| ≤ N‖α‖ with N := (P^n)^{1/2}, ‖α‖ the operator norm of the continuous alternating map α, because |α(e_{I_1}, …, e_{I_n})| ≤ ‖α‖·Π_i ‖e_{I_i}‖ = ‖α‖ and there are at most P^n tuples I.
2. (Sup norm of a test form.) For ω ∈ 𝒟ⁿ(U), x ↦ |ω(x)| is continuous (step 1) and vanishes outside the compact set tsupport ω, hence bounded; put ‖ω‖_∞ := sup_x |ω(x)| < ∞.
3. (Basic estimate.) Let X ∈ 𝒟_n(U) with M(X) < ∞, ω ∈ 𝒟ⁿ(U) and c > 0 with |ω(x)| ≤ c for all x. Then |X(ω)| ≤ c·M(X)^ℝ, where M(X)^ℝ := M(X).toReal. Indeed c⁻¹ω and −c⁻¹ω belong to 𝒟ⁿ(U) (same tsupport) and |±c⁻¹ω(x)| = c⁻¹|ω(x)| ≤ 1, so both are admissible; by the definition of M = M_U, ENNReal.ofReal(±c⁻¹X(ω)) ≤ M(X), i.e. ±X(ω) ≤ c·M(X)^ℝ.
4. (Definition of Y.) Put s := Σ_r M(X_r) < ∞. Then every M(X_r) is finite, the real sequence r ↦ M(X_r)^ℝ is summable (Mathlib ENNReal.summable_toReal) and Σ_r M(X_r)^ℝ = s^ℝ (ENNReal.tsum_toReal_eq). For ω ∈ 𝒟ⁿ(U) let c_ω := ‖ω‖_∞ + 1 > 0. By step 3, |X_r(ω)| ≤ c_ω·M(X_r)^ℝ for every r, so the real series Σ_r X_r(ω) is absolutely summable (Summable.of_norm_bounded). Define Y(ω) := Σ_r X_r(ω); thus HasSum (r ↦ X_r(ω)) (Y(ω)).
5. (Linearity.) For ω, ω' ∈ 𝒟ⁿ(U) and t ∈ ℝ, X_r(ω + ω') = X_r(ω) + X_r(ω') and X_r(tω) = t·X_r(ω) for every r; by HasSum.add, HasSum.mul_left and uniqueness of sums, Y(ω + ω') = Y(ω) + Y(ω') and Y(tω) = t·Y(ω). So Y is a linear functional on 𝒟ⁿ(U).
6. (Uniform bound.) If c > 0 and |ω(x)| ≤ c for all x, then |Y(ω)| ≤ Σ_r |X_r(ω)| ≤ Σ_r c·M(X_r)^ℝ = c·s^ℝ (steps 3 and 4).
7. (Sequential continuity.) Let ω_k → 0 in 𝒟ⁿ(U) (TestFormOnConverges ω_k 0): there is a compact K ⊆ U with tsupport ω_k ⊆ K for all k and ω_k → 0 uniformly on K (the derivative of order 0; the order-0 iterated derivative has the same norm as the form). Since ω_k = 0 outside K, ε_k := sup_x ‖ω_k(x)‖ → 0, and by step 1, |ω_k(x)| ≤ N·ε_k for all x. Step 6 with c := N·ε_k + 1/(k + 1) > 0 gives |Y(ω_k)| ≤ (N·ε_k + 1/(k + 1))·s^ℝ → 0. Hence Y is sequentially continuous; together with step 5 it is a current Y ∈ 𝒟_n(U), and HasSum (r ↦ X_r(ω)) (Y(ω)) for every ω by step 4.
8. (Mass.) Let ω be admissible. The terms max(X_r(ω), 0) are nonnegative and dominated by |X_r(ω)|, so they are summable, and X_r(ω) ≤ max(X_r(ω), 0) termwise; hence Y(ω) = Σ_r X_r(ω) ≤ Σ_r max(X_r(ω), 0) (Mathlib Summable.tsum_le_tsum) and ENNReal.ofReal(Y(ω)) ≤ ENNReal.ofReal(Σ_r max(X_r(ω), 0)) = Σ_r ENNReal.ofReal(X_r(ω)) (ENNReal.ofReal_tsum_of_nonneg) ≤ Σ_r M(X_r), because ENNReal.ofReal(X_r(ω)) ≤ M(X_r) for each r (ω is admissible). Taking the supremum over admissible ω gives M(Y) ≤ Σ_r M(X_r). ∎

## Key steps

1. For |ω| ≤ c, admissibility of ±c⁻¹ω gives |X(ω)| ≤ c·M(X).
2. Mass-summability makes Σ_r X_r(ω) absolutely convergent; Y(ω) is its sum and is linear by uniqueness of sums.
3. |Y(ω)| ≤ c·Σ_r M(X_r) whenever |ω| ≤ c, and uniform convergence of ω_k → 0 gives sequential continuity.
4. ENNReal.ofReal(X_r(ω)) ≤ M(X_r) for admissible ω yields M(Y) ≤ Σ_r M(X_r).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n "cmc_fc_|flat.?conver|deformation|slic" local-references/123e8435b4a2469b/project/GMT --glob '*.lean'`
- `rg -n -i "flat norm|flat convergence|deformation theorem|federer.?fleming" local-references/123e8435b4a2469b/mathlib/Mathlib --glob '*.lean' (no match)`
- `rg -n "theorem FiniteMeasure.limsup_measure_closed_le_of_tendsto|theorem Monotone.ae_differentiableAt|theorem MonotoneOn.intervalIntegral_deriv_mem_uIcc|theorem measurable_deriv |theorem tendsto_of_subseq_tendsto|theorem extraction_of_frequently_atTop |theorem exists_contMDiffMap_one_nhds_of_subset_interior|theorem lipschitz_infDist_pt|theorem _root_.IsCompact.exists_cthickening_subset_open|theorem integral_withDensity_eq_integral_smul |theorem lintegral_liminf_le " local-references/123e8435b4a2469b/mathlib/Mathlib --glob '*.lean'`
- `rg -n "theorem HasDerivAt.tendsto_slope_zero_left|theorem ENNReal.tsum_geometric|theorem Finite.exists_infinite_fiber|theorem countable_meas_level_set_pos|theorem ENNReal.ofReal_tsum_of_nonneg|theorem withDensity_absolutelyContinuous|theorem tendsto_measure_iInter_atTop|theorem Summable.of_norm_bounded " local-references/123e8435b4a2469b/mathlib/Mathlib --glob '*.lean'`
- `grep -n '^def \|^theorem \|^structure ' in lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean; grep -n 'theorem simon_theorem_4_16_compact_metrizable\|theorem finiteMeasure_tendsto_subseq_of_compact_metrizable' Chapter01/CompactMetrizableCompactness.lean; grep -n 'countablyRectifiable_of_measure_zero' Chapter03/Rectifiable.lean`
- `python3 scan of dag.json: siblings of root.compactness_of_minimizing_currents-a1 and their frozen types; cross-parent dependency edges (only accepted nodes); accepted reusable declarations (dtc_vanish_off_support, dtc_isIntegerMultiplicity_sub, dtc_extend_by_zero, dtc_restrictDomain_isIntegerMultiplicity, dor_imrep_massOn_eq_measure_and_support, rsd_cmr_imrep_restrict, dor_ims_unitOrientation_dual); collisions of the seven cmc_fc_* names (none)`
- `sed -n 1790,1960p, 2000,2200p, 3150,3260p, 5071,5200p, 6480,6620p /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py (_solve_children, _existing_lean_name_problem, _overlay_accepted_children, _node_worktree, _leaf_author_task)`
- `sed -n 2004,2140p book/chapter-06.txt (Simon Ch. 6, 7.1–7.2)`
- `lake env lean /tmp/fcdec/Types.lean (8 child types + 5 conjunct projections); lake env lean /tmp/fcdec/Assembly.lean (#print axioms fc_assembly); lake env lean /tmp/fcdec/Inst.lean (pp.explicit Sub instance); lake env lean /tmp/fcdec/Avail.lean … /tmp/fcdec/Avail5.lean (#check probes of the import closure of GMT.Ch07.Submission)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Portmanteau.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-v5.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/fcdec/Types.lean`
- `/tmp/fcdec/Assembly_checked.lean`
- `/tmp/fcdec/Inst.lean`
- `/tmp/fcdec/Avail.lean`
- `/tmp/fcdec/Avail2.lean`
- `/tmp/fcdec/Avail3.lean`
- `/tmp/fcdec/Avail4.lean`
- `/tmp/fcdec/Avail5.lean`

The snapshot (project b4d606db, mathlib 25730c7c) Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. The snapshot has no cmc_fc_ declaration. Neither the snapshot project nor Mathlib proves slicing, deformation, closure or flat convergence; the Ch06 contract only states slices as its own frozen sorry. These therefore remain the parent's prerequisite theorems and reach the children as exact antecedents. The pinned Mathlib supplies the elementary tools the children cite: isCompact_univ_pi, IsCompact.tendsto_subseq, tendsto_pi_nhds, Monotone.countable_not_continuousAt, lintegral_liminf_le, lintegral_lintegral_swap, measurable_measure_prodMk_left, Filter.Tendsto.liminf_le_liminf_comp, exists_contMDiffMap_one_nhds_of_subset_interior, IsCompact.exists_cthickening_subset_open, lipschitz_infDist_pt, integral_withDensity_eq_integral_smul, withDensity_absolutelyContinuous, Finite.exists_infinite_fiber, ENNReal.tsum_geometric and HasSum.tendsto_sum_nat. #check confirms all of them after import GMT.Ch07.Submission. FiniteMeasure.limsup_measure_closed_le_of_tendsto, MonotoneOn.intervalIntegral_deriv_mem_uIcc and SimonGMT finiteMeasure_tendsto_subseq_of_compact_metrizable exist in the pinned sources but lie outside that import closure, so good_slice avoids them. Among accepted DAG declarations, dtc_vanish_off_support is reused with its identical type. The eight child types elaborate, and the conditional assembly of the exact parent type compiles with only propext, Classical.choice and Quot.sound.
