# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.series_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, proof of Theorem 7.2, "by 3.13 we can define integer multiplicity R^(ℓ), S^(ℓ) by the M-absolutely convergent series R^(ℓ) = Σ_{r≥ℓ} R_r, S^(ℓ) = Σ_{r≥ℓ} S_r; then M(R^(ℓ)) + M(S^(ℓ)) ≤ 2^{−ℓ+1} and T − T_{j_ℓ} = ∂R^(ℓ) + S^(ℓ)", i.e. step 6 of the parent proof, with Lemma 3.13 replaced by the closure theorem (CL). Fix ℓ ∈ ℕ.
1. (Sums and mass subadditivity.) For currents A, B with the same domain put A ⊕ B := A − ((B − B) − B); evaluating, (A ⊕ B)(ω) = A(ω) + B(ω), and (∂(A ⊕ B))(η) = ∂A(η) + ∂B(η). If A and B are IM, then B − B, (B − B) − B and A ⊕ B are IM by (IS) (U is open). For every G, M_G(A ⊕ B) ≤ M_G(A) + M_G(B) and M_G(A − B) ≤ M_G(A) + M_G(B) (F1): for ω admissible for M_G, −ω is admissible too, (A ⊕ B)(ω) = A(ω) + B(ω), (A − B)(ω) = A(ω) + B(−ω), and ENNReal.ofReal(s + t) ≤ ENNReal.ofReal(s) + ENNReal.ofReal(t).
2. (Partial sums.) Define R^0 := R_ℓ, R^{N+1} := R^N ⊕ R_{ℓ+N+1}, and S^0 := S_ℓ, S^{N+1} := S^N ⊕ S_{ℓ+N+1}. By induction on N and step 1: R^N and S^N are IM, R^N(ω) = Σ_{r=ℓ}^{ℓ+N} R_r(ω), S^N(ω) = Σ_{r=ℓ}^{ℓ+N} S_r(ω), and M(R^N) ≤ Σ_{r=ℓ}^{ℓ+N} M(R_r) ≤ Σ_r 2^{−r} = 2, M(S^N) ≤ 2.
3. (Telescoping.) For every N, X_{ℓ+N+1} − X_ℓ − S^N = ∂R^N. For N = 0 this is the hypothesis at r = ℓ. If it holds for N, evaluate at ω ∈ 𝒟^{m+1}(U) and add the hypothesis at r = ℓ + N + 1, X_{ℓ+N+2}(ω) − X_{ℓ+N+1}(ω) − S_{ℓ+N+1}(ω) = R_{ℓ+N+1}(dω): this gives X_{ℓ+N+2}(ω) − X_ℓ(ω) − S^{N+1}(ω) = R^N(dω) + R_{ℓ+N+1}(dω) = R^{N+1}(dω) = ∂R^{N+1}(ω).
4. (Boundary of S^N.) For η ∈ 𝒟^m(U), dη ∈ 𝒟^{m+1}(U) and d(dη) = 0, so step 3 at dη gives ∂X_{ℓ+N+1}(η) − ∂X_ℓ(η) − ∂S^N(η) = R^N(d dη) = R^N(0) = 0. Hence ∂S^N(η) = (∂X_{ℓ+N+1} − ∂X_ℓ)(η), and by (F1) M_G(∂S^N) ≤ M(∂X_{ℓ+N+1}) + M(∂X_ℓ) ≤ 2Λ for every G ⊆ U.
5. (Series currents.) Σ_r M(R_{ℓ+r}) ≤ Σ_r 2^{−(ℓ+r)} = 2·2^{−ℓ} < ∞, so the sibling series_current gives R' ∈ 𝒟_{m+2}(U) with HasSum (r ↦ R_{ℓ+r}(ω)) (R'(ω)) for every ω and M(R') ≤ Σ_r M(R_{ℓ+r}); likewise it gives S' ∈ 𝒟_{m+1}(U) for (S_{ℓ+r})_r with M(S') ≤ Σ_r M(S_{ℓ+r}). Partial sums of a convergent series converge to its sum (Mathlib HasSum.tendsto_sum_nat), so R^N(ω) → R'(ω) and S^N(ω) → S'(ω) as N → ∞ for every test form ω; i.e. R^N ⇀ R' and S^N ⇀ S' in U.
6. (R' and S' are IM.) Let G be open with closure(G) compact and contained in U, so G ⊆ U and M_G ≤ M_U. For every N: M_G(R^N) ≤ 2; by step 3 and (F1), M_G(∂R^N) = M_G(X_{ℓ+N+1} − X_ℓ − S^N) ≤ M(X_{ℓ+N+1}) + M(X_ℓ) + M(S^N) ≤ 2Λ + 2; M_G(S^N) ≤ 2; and M_G(∂S^N) ≤ 2Λ by step 4. Hence sup_N (M_G(R^N) + M_G(∂R^N)) < ∞ and sup_N (M_G(S^N) + M_G(∂S^N)) < ∞ (in degrees m + 2 and m + 1 the contract's boundaryMassOn is the mass of the boundary). The currents R^N and S^N are IM (step 2) and converge weakly to R' and S' (step 5), so (CL), applied with d := m + 2 and with d := m + 1, shows that R' and S' are IM.
7. (Identity.) For ω ∈ 𝒟^{m+1}(U), step 3 gives X_{ℓ+N+1}(ω) − X_ℓ(ω) − S^N(ω) = R^N(dω). As N → ∞, X_{ℓ+N+1}(ω) → X_lim(ω) (X_r ⇀ X_lim), S^N(ω) → S'(ω) and R^N(dω) → R'(dω) (step 5 with dω ∈ 𝒟^{m+2}(U)). Hence X_lim(ω) − X_ℓ(ω) − S'(ω) = R'(dω) = ∂R'(ω), i.e. X_lim − X_ℓ − S' = ∂R'.
8. (Mass.) M(R') + M(S') ≤ Σ_r M(R_{ℓ+r}) + Σ_r M(S_{ℓ+r}) = Σ_r (M(R_{ℓ+r}) + M(S_{ℓ+r})) ≤ Σ_r 2^{−(ℓ+r)} = 2^{−ℓ}·Σ_r 2^{−r} = 2·2^{−ℓ} (ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_geometric). ∎

## Key steps

1. Partial sums R^N, S^N are IM by (IS), telescope to X_{ℓ+N+1} − X_ℓ − S^N = ∂R^N, and ∂S^N = ∂X_{ℓ+N+1} − ∂X_ℓ.
2. The sibling series_current turns the mass-summable tails into currents R', S' that are weak limits of the partial sums, with masses bounded by the tail sums.
3. Uniform bounds on M + M∂ of the partial sums let (CL) show that R' and S' are integer multiplicity.
4. Passing to the limit gives X_lim − X_ℓ − S' = ∂R' and M(R') + M(S') ≤ 2·2^{−ℓ}.

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
