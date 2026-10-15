# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.minimizing_and_measures-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.minimizing_and_measures-a1.minimality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof (Simon 7.2.4, (8) and its localization: chapter-07.txt lines 226–229, with the comparison (12), line 260, and the lower semicontinuity of lines 262–263). Siblings used: mass_lsc (the parent's L3), mass_eq_measure (the parent's L2), mass_agree_off_support (the parent's use of V: S and C agree on forms supported in O = ℝ^P ∖ spt(S − C)), and measure_agree_on_borel with imrep_local_finiteness, which together with the previous two give the case U₁ = U₂ = ℝ^P, W := O of MEAS that the parent applies ('μ_S = μ_C on Borel subsets of O, in particular on W ∖ W′'). The argument is the parent's, step for step; only the appeal to MEAS is unfolded into these accepted components (MEAS is not available to a child of this node). Notation: M_G(T) = T.massOn G; all quantities lie in [0, ∞].
1. IsMinimizingIn C ℝ^P has two parts. The first, IsIntegerMultiplicity C, is a hypothesis. For the second, fix an open W with CompactlyContained W ℝ^P and an integer multiplicity S ∈ 𝒟_n(ℝ^P) with SameBoundary S C such that K := spt(S − C) is compact and K ⊆ ℝ^P ∩ W = W. We must show M_W(C) ≤ M_W(S).
2. K is compact, W is open and K ⊆ W, so there is ε > 0 with thickening(ε, K) ⊆ W (Mathlib IsCompact.exists_thickening_subset_open).
3. Apply hypothesis (3) with K, ε and ψ := id, which is strictly increasing. This gives an open W′ with K ⊆ W′ ⊆ thickening(ε, K) ⊆ W and a strictly increasing φ′ such that limsup_i M_{W′}(S_{φ′(i)}) ≤ M_{W′}(S′) for every integer multiplicity S′ ∈ 𝒟_n(ℝ^P) with SameBoundary S′ C and spt(S′ − C) ⊆ K. S itself qualifies, since spt(S − C) = K ⊆ K. Hence limsup_i M_{W′}(S_{φ′(i)}) ≤ M_{W′}(S).
4. By mass_lsc with φ := φ′ and O := W′: M_{W′}(C) ≤ liminf_i M_{W′}(S_{φ′(i)}) ≤ limsup_i M_{W′}(S_{φ′(i)}) ≤ M_{W′}(S). Here liminf ≤ limsup holds along atTop in the complete lattice [0, ∞].
5. Let R_C and R_S be integer multiplicity representations of C and S (they exist by IsIntegerMultiplicity C and IsIntegerMultiplicity S), and put μ_C := R_C.measure and μ_S := R_S.measure. By mass_eq_measure (U := ℝ^P, which is open), M_G(C) = μ_C(G) and M_G(S) = μ_S(G) for every open G ⊆ ℝ^P.
6. O := ℝ^P ∖ K is open, since K is compact and hence closed. Let G ⊆ O be open. Then G ∩ K = ∅ and spt(S − C) ⊆ K, so mass_agree_off_support (with U := ℝ^P, S := S, T := C, K := K, G := G) gives M_G(S) = M_G(C). By step 5, μ_S(G) = μ_C(G).
7. By imrep_local_finiteness (with U := ℝ^P and R := R_S), μ_S(K′) ≠ ∞ for every compact K′ ⊆ ℝ^P, in particular for every compact K′ ⊆ O. By measure_agree_on_borel (with O, μ := μ_S and ν := μ_C), using step 6 and this finiteness, μ_S(A) = μ_C(A) for every Borel set A ⊆ O.
8. W ∖ W′ is a Borel set (a difference of open sets) and W ∖ W′ ⊆ O because K ⊆ W′. By step 7, μ_S(W ∖ W′) = μ_C(W ∖ W′).
9. W′ ⊆ thickening(ε, K) ⊆ W and W′ is Borel, so μ(W) = μ(W′) + μ(W ∖ W′) for every measure μ on ℝ^P (Mathlib measure_inter_add_sdiff with W ∩ W′ = W′). Using steps 4, 5 and 8: M_W(C) = μ_C(W) = μ_C(W′) + μ_C(W ∖ W′) = M_{W′}(C) + μ_S(W ∖ W′) ≤ M_{W′}(S) + μ_S(W ∖ W′) = μ_S(W′) + μ_S(W ∖ W′) = μ_S(W) = M_W(S). These manipulations are valid in [0, ∞] without any finiteness assumption (addition is monotone in [0, ∞]).
10. Since W and S were arbitrary, C is minimizing in ℝ^P (IsMinimizingIn C univ). ∎

## Key steps

1. For a competitor S with K := spt(S − C) compact and ⊆ W, choose ε with thickening(ε, K) ⊆ W and apply the local comparison with ψ = id: an open W′ with K ⊆ W′ ⊆ W and φ′ with limsup_i M_{W′}(S_{φ′(i)}) ≤ M_{W′}(S).
2. mass_lsc along φ′ and liminf ≤ limsup give M_{W′}(C) ≤ M_{W′}(S).
3. mass_eq_measure turns masses on open sets into weights; mass_agree_off_support gives μ_S = μ_C on open subsets of O = ℝ^P ∖ K, and measure_agree_on_borel with imrep_local_finiteness extends this to Borel subsets of O, in particular W ∖ W′.
4. Additivity: μ_C(W) = μ_C(W′) + μ_C(W ∖ W′) ≤ μ_S(W′) + μ_S(W ∖ W′) = μ_S(W), i.e. M_W(C) ≤ M_W(S).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c); cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `grep -n 'def \|theorem ' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean (massAdmissibleOn, GeometricCurrentOn.massOn, massOn_mono, le_massOn, WeaklyConvergesOn.massOn_le_liminf: fixed domain only)`
- `grep -n 'def \|theorem ' simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean (VanishesOn, zeroRegion, support, support_subset_domain)`
- `grep -rn over local-references/123e8435b4a2469b/mathlib/Mathlib: 'exists_thickening_subset_open|tendsto_measure_thickening_of_isClosed|extraction_of_frequently_atTop|frequently_lt_of_lt_limsup|le_limsup_of_frequently_le|liminf_le_limsup|measure_inter_add_sdiff|IsCompact.cthickening|thickening_subset_cthickening|StrictMono.tendsto_atTop|Tendsto.liminf_eq|tendsto_ofReal|isBounded_iff_subset_closedBall' (all found; also exists_between at Order/Basic.lean:982, Bornology.IsBounded.subset_closedBall at Topology/MetricSpace/Bounded.lean:101, and liminf_le_liminf generated by @[to_dual] from limsup_le_limsup at Order/LiminfLimsup.lean:158–159, so a plain grep for 'theorem liminf_le_liminf' has no match)`
- `python3 -I over runs/20261011T150044Z-ba604216b4/dag.json: status, candidate_commit, updated_at, parent, depends_on and lean_statement of cmc_massOn_eq_imRep_measure, dtc_vanish_off_support, cmc_ml_massOn_eq_of_disjoint_sub_support, cmc_ml_measure_eq_of_eq_on_open_subsets, rsd_imrep_compact_measure_ne_top, cmc_massOn_le_of_le_near_support, dtc_bc_measure_restrict_eq_of_eqOn, dtc_bc_tendsto_integral_of_limsup_liminf`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint|_solve_children|_install_parent_supplied_child_handoff|_overlay_accepted_children|refresh' /runtime/flows/gmt-claude-b731e326000c/_recursive_lean/{runtime,store,parallel}.py; ps -o pid,lstart,cmd for the dedicated run-workflow process 52190 (started 06:07Z, issue 4761)`
- `git show 27de75e / 44ef61f / 2c8f61f / 9adc8b2 / 702e708 :GMT/Ch07/Submission.lean (declaration blocks merged into /tmp/mm-decomp4/lean/Merged.lean)`
- `lake env lean /tmp/mm-decomp4/lean/EndToEnd.lean, /tmp/mm-decomp4/lean/Merged.lean (#print axioms) and /tmp/mm-decomp4/lean/Challenge_<key>.lean for all nine children and the parent`
- `python3 -I verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py layout('07') + child_modules(contract mode) on all ten types; runtime ScopedDecomposition, Runtime._dependency_problem and Runtime._topological on this answer`
- `grep -rl dtc_bc_mm_ over dag.json, runs/.../nodes, GMT, simongmt/Poincare; git log --all -S'dtc_bc_mm_' -- GMT (only this node's rejected decomposition-v1.json)`
- `grep -n '^(8)|(12)|(13)|(14)|We actually only proved|trivially lower semi' book/chapter-07.txt book/chapter-06.txt (lines 226, 228, 260, 262, 276, 278, 283, 285; chapter-06 line 313)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Tendsto.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-minimizing-an-5607bbe9ea/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-minimizing-an-5607bbe9ea/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-equals-rep-measure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-minimality-localizes-a1-ma-bcdb5ddd33/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-minimality-localizes-a1-me-9255eab117/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-imrep-local-finiteness-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b731e326000c/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b731e326000c/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b731e326000c/_recursive_lean/parallel.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/mm-decomp4/lean/Merged.lean`
- `/tmp/mm-decomp4/lean/EndToEnd.lean`

The snapshot contract (project b4d606d, Mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean. The pinned SimonGMT library supplies massAdmissibleOn, massOn and le_massOn, the TestFormOn and currentEval coercions, the GeometricCurrentOn Zero and Sub structure, zeroRegion and support. Its WeaklyConvergesOn.massOn_le_liminf covers only a fixed domain, so lower semicontinuity under ConvergesWeakly on exhausting domains becomes the new child mass_lsc. Every Mathlib lemma the new proofs cite exists at the pin (Thickening.lean, BorelSpace/Metric.lean, AtTopBot/Basic.lean and AtTopBot/Tendsto.lean, Order/LiminfLimsup.lean, Topology/Order/LiminfLimsup.lean, Measure/Basic.lean). The five reused DAG declarations are comparator-accepted at byte-identical types: candidates 27de75e, 44ef61f, 2c8f61f, 9adc8b2, 702e708. Merged with complete Lean proofs of the four new children, they compile with propext, Classical.choice and Quot.sound only, and they derive the exact selected type with only the RADON dependency stubbed. cmc_massOn_le_of_le_near_support is not used. No dtc_bc_mm_ name is reserved anywhere.
