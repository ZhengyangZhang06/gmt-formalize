# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.measure_subadditive-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.measure_subadditive-a1.open_to_borel-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3–6 of the selected parent proof, stated for abstract measures μ (the parent's μ_Z) and ν (the parent's μ_X + μ_Y). These steps extend the open-set inequality μ_Z(V) ≤ μ_X(V) + μ_Y(V) (V ⊆ U open) to all Borel sets "by outer regularity of these locally finite Borel measures". As in the parent's step 5, outer regularity is applied to a finite restriction to V_k. Only the restriction ν⌞V_k is needed, because the parent's step 5(c) uses only the ν-part of λ = (μ_X + μ_Y + μ_Z)⌞V_k. Therefore no finiteness of μ on compact sets is assumed. The outer regularity used is Simon, Ch. 1, Theorem 1.15(1) (book/chapter-01.txt lines 274–285), applied to the finite Borel measure ν⌞V_k on the metric space ℝ^P. The parent's exhaustion of step 4 is written with the extended distance to ℝ^P ∖ U, so the case U = ℝ^P needs no separate treatment.

Hypotheses. U ⊆ ℝ^P is open, and μ, ν are measures on the Borel sets of ℝ^P (Mathlib Measure (Euclid P), evaluated on arbitrary sets as outer measures). They satisfy:
(i) μ(ℝ^P ∖ U) = 0;
(ii) ν(K) < ∞ for every compact K ⊆ U;
(iii) μ(V) ≤ ν(V) for every open V ⊆ U.

Notation. For x ∈ ℝ^P let d(x) := inf{‖x − y‖ : y ∈ ℝ^P ∖ U} ∈ [0, ∞] be the extended distance from x to ℝ^P ∖ U (Mathlib Metric.infEDist x Uᶜ). If U = ℝ^P then d ≡ +∞. In [0, ∞], 1/0 = +∞ and 1/k > 0 for every k ∈ ℕ. For k ∈ ℕ put
V_k := {x ∈ ℝ^P : ‖x‖ < k and 1/k < d(x)},
K_k := {x ∈ ℝ^P : ‖x‖ ≤ k and 1/k ≤ d(x)}.

1. (Topology.) The function d is continuous (it is 1-Lipschitz for the extended metric; Mathlib continuous_infEDist), and so is x ↦ ‖x‖. Hence V_k is open, being the intersection of the strict sublevel set {‖x‖ < k} and the strict superlevel set {d > 1/k}. K_k is closed for the same reason with weak inequalities. K_k ⊆ closedBall(0, k) is bounded, so K_k is compact, since closed bounded subsets of ℝ^P are compact.
2. (K_k ⊆ U and V_k ⊆ K_k.) If x ∉ U, then x ∈ ℝ^P ∖ U, so d(x) = 0 < 1/k and x ∉ K_k; thus K_k ⊆ U. Strict inequalities imply weak ones, so V_k ⊆ K_k ⊆ U.
3. (Monotone exhaustion.) If k ≤ m and x ∈ V_k, then ‖x‖ < k ≤ m and 1/m ≤ 1/k < d(x), so x ∈ V_m; thus (V_k) is increasing. By step 2, ⋃_k V_k ⊆ U. Conversely, let x ∈ U. The set ℝ^P ∖ U is closed and does not contain x, so d(x) > 0 (Mathlib infEDist_pos_iff_notMem_closure). Choose a ∈ ℕ with 1/a < d(x) (possible as d(x) > 0; Mathlib ENNReal.exists_inv_nat_lt) and b ∈ ℕ with ‖x‖ < b, and let k := max(a, b). Then ‖x‖ < b ≤ k and 1/k ≤ 1/a < d(x), so x ∈ V_k. Hence ⋃_k V_k = U.
4. (Finiteness.) By step 2 and hypothesis (ii) applied to the compact set K_k ⊆ U, ν(V_k) ≤ ν(K_k) < ∞.
5. (Comparison inside V_k.) Fix k and an arbitrary set E ⊆ ℝ^P. Let ν_k := ν⌞V_k. Since V_k is Borel, ν_k(A) = ν(A ∩ V_k) for every A ⊆ ℝ^P. By step 4, ν_k is a finite Borel measure on the metric space ℝ^P. Hence it is outer regular: for every A ⊆ ℝ^P and every r > ν_k(A) there is an open O ⊇ A with ν_k(O) < r. This is Simon 1.15(1). In Mathlib, a finite measure on a pseudo-metrizable Borel space is weakly regular (instance WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure), hence outer regular (Set.exists_isOpen_lt_of_lt).
We claim μ(E ∩ V_k) ≤ ν(E ∩ V_k). It suffices to show μ(E ∩ V_k) < r for every r ∈ [0, ∞] with ν(E ∩ V_k) < r: if instead ν(E ∩ V_k) < μ(E ∩ V_k), then r := μ(E ∩ V_k) would violate this. So let ν(E ∩ V_k) < r. Then ν_k(E) = ν(E ∩ V_k) < r, so there is an open O ⊇ E with ν(O ∩ V_k) = ν_k(O) < r. The set O ∩ V_k is open (step 1) and contained in V_k ⊆ U (step 2). Hypothesis (iii) and monotonicity of μ give
μ(E ∩ V_k) ≤ μ(O ∩ V_k) ≤ ν(O ∩ V_k) < r.
6. (Concentration on U.) Let E be a Borel set. U is open, hence Borel, so μ(E) = μ(E ∩ U) + μ(E ∖ U). By hypothesis (i), μ(E ∖ U) ≤ μ(ℝ^P ∖ U) = 0. Hence μ(E) = μ(E ∩ U).
7. (Continuity from below.) By step 3, the sets E ∩ V_k increase with k and their union is E ∩ U. By continuity of μ from below (Mathlib Monotone.measure_iUnion), μ(E ∩ U) = sup_k μ(E ∩ V_k). By step 5 and monotonicity of ν, μ(E ∩ V_k) ≤ ν(E ∩ V_k) ≤ ν(E) for every k. With step 6, μ(E) = μ(E ∩ U) ≤ ν(E).
8. (Conclusion.) Step 7 holds for every Borel set E. An inequality between measures may be checked on measurable sets (Mathlib Measure.le_iff), so μ ≤ ν, i.e. μ(E) ≤ ν(E) for every E ⊆ ℝ^P. ∎

Appendix (verified Lean realization of the numbered proof above; not part of the proof). The declaration below was compiled in this decomposition session with Lean v4.35.0-rc3 and Mathlib 25730c7c. It was placed after `import GMT.Ch07.Submission` in the child comparator scope: inside `namespace GMT.Ch07` with the frozen contract's `open` commands, after its `noncomputable section ... end`. `exact Submission.dtc_bc_lc_measure_le_of_le_on_open` closes the frozen type, and `#print axioms` reports only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.dtc_bc_lc_measure_le_of_le_on_open : ∀ (P : ℕ) (U : Set (Euclid P)) (μ ν : Measure (Euclid P)), IsOpen U → μ Uᶜ = 0 → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ν K < ∞) → (∀ V : Set (Euclid P), IsOpen V → V ⊆ U → μ V ≤ ν V) → μ ≤ ν := by
  intro P U μ ν hU hμU hν hle
  -- Steps 1–3: the exhaustion `V k ⊆ K k ⊆ U`, `V` increasing with union `U`
  set V : ℕ → Set (Euclid P) :=
    fun k => {x | ‖x‖ < k ∧ (k : ℝ≥0∞)⁻¹ < infEDist x Uᶜ} with hVdef
  set K : ℕ → Set (Euclid P) :=
    fun k => {x | ‖x‖ ≤ k ∧ (k : ℝ≥0∞)⁻¹ ≤ infEDist x Uᶜ} with hKdef
  have hVopen : ∀ k, IsOpen (V k) := fun k =>
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const continuous_infEDist)
  have hKcpt : ∀ k, IsCompact (K k) := fun k => by
    refine isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le continuous_norm continuous_const).inter
        (isClosed_le continuous_const continuous_infEDist)
    · refine (isBounded_closedBall (x := (0 : Euclid P)) (r := (k : ℝ))).subset ?_
      intro x hx
      simpa [mem_closedBall, dist_zero_right] using hx.1
  have hKU : ∀ k, K k ⊆ U := fun k x hx => by
    by_contra hxU
    have h0 : infEDist x Uᶜ = 0 := infEDist_zero_of_mem hxU
    have h1 : (k : ℝ≥0∞)⁻¹ ≤ 0 := h0 ▸ hx.2
    exact (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top k)) (nonpos_iff_eq_zero.mp h1)
  have hVK : ∀ k, V k ⊆ K k := fun k x hx => ⟨hx.1.le, hx.2.le⟩
  have hVmono : Monotone V := fun k m hkm x hx =>
    ⟨lt_of_lt_of_le hx.1 (by exact_mod_cast hkm),
      lt_of_le_of_lt (ENNReal.inv_le_inv.mpr (by exact_mod_cast hkm)) hx.2⟩
  have hVU : ⋃ k, V k = U := by
    apply subset_antisymm
    · exact iUnion_subset fun k => (hVK k).trans (hKU k)
    · intro x hx
      have hpos : 0 < infEDist x Uᶜ := by
        rw [infEDist_pos_iff_notMem_closure, hU.isClosed_compl.closure_eq]
        exact fun h => h hx
      obtain ⟨a, ha⟩ := ENNReal.exists_inv_nat_lt hpos.ne'
      obtain ⟨b, hb⟩ := exists_nat_gt ‖x‖
      refine mem_iUnion.mpr ⟨max a b, ?_, ?_⟩
      · exact lt_of_lt_of_le hb (by exact_mod_cast le_max_right a b)
      · exact lt_of_le_of_lt (ENNReal.inv_le_inv.mpr (by exact_mod_cast le_max_left a b)) ha
  -- Step 4: `ν (V k) < ∞`
  have hνV : ∀ k, ν (V k) ≠ ∞ := fun k =>
    ne_of_lt (lt_of_le_of_lt (measure_mono (hVK k)) (hν _ (hKcpt k) (hKU k)))
  -- Step 5: comparison inside `V k`, by outer regularity of the finite measure `ν⌞V k`
  have hcomp : ∀ k (E : Set (Euclid P)), μ (E ∩ V k) ≤ ν (E ∩ V k) := by
    intro k E
    have : IsFiniteMeasure (ν.restrict (V k)) := isFiniteMeasure_restrict.mpr (hνV k)
    refine le_of_forall_gt fun r hr => ?_
    rw [← Measure.restrict_apply' (hVopen k).measurableSet] at hr
    obtain ⟨O, hEO, hO, hOr⟩ := Set.exists_isOpen_lt_of_lt E r hr
    rw [Measure.restrict_apply' (hVopen k).measurableSet] at hOr
    calc μ (E ∩ V k) ≤ μ (O ∩ V k) := measure_mono (inter_subset_inter_left _ hEO)
      _ ≤ ν (O ∩ V k) := hle _ (hO.inter (hVopen k))
          (inter_subset_right.trans ((hVK k).trans (hKU k)))
      _ < r := hOr
  -- Steps 6–8: concentration on `U`, continuity from below, `Measure.le_iff`
  rw [Measure.le_iff]
  intro E hE
  calc μ E = μ (E ∩ U) := by
        have h := measure_inter_add_sdiff E hU.measurableSet (μ := μ)
        have h2 : μ (E \ U) = 0 := measure_mono_null (fun x hx => hx.2) hμU
        rw [h2, add_zero] at h
        exact h.symm
    _ = ⨆ k, μ (E ∩ V k) := by
        rw [← hVU, inter_iUnion]
        exact Monotone.measure_iUnion fun k m hkm => inter_subset_inter_right E (hVmono hkm)
    _ ≤ ν E := iSup_le fun k => (hcomp k E).trans (measure_mono inter_subset_left)
```

## Key steps

1. Exhaust U by the open sets V_k = {‖x‖ < k, 1/k < d(x, ℝ^P ∖ U)} (extended distance). They increase with union U, and each lies in the compact set K_k = {‖x‖ ≤ k, 1/k ≤ d(x, ℝ^P ∖ U)} ⊆ U, so ν(V_k) < ∞ by (ii).
2. ν⌞V_k is a finite Borel measure on the metric space ℝ^P, hence outer regular (Simon 1.15(1); Mathlib WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure).
3. For any E and open O ⊇ E, μ(E ∩ V_k) ≤ μ(O ∩ V_k) ≤ ν(O ∩ V_k) by (iii), since O ∩ V_k ⊆ U is open. Outer regularity of ν⌞V_k then gives μ(E ∩ V_k) ≤ ν(E ∩ V_k).
4. For Borel E: μ(E) = μ(E ∩ U) by (i), μ(E ∩ U) = sup_k μ(E ∩ V_k) by continuity from below, and this is ≤ ν(E). Measure.le_iff gives μ ≤ ν.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c); cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `rg -n 'theorem _root_.Set.exists_isOpen_lt_of_lt|instance \(priority := 100\) of_pseudoMetrizableSpace_of_isFiniteMeasure|class WeaklyRegular' mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `grep -n '^theorem\|^lemma\|^instance' mathlib/Mathlib/MeasureTheory/Measure/Regular.lean | grep -i 'outer\|restrict\|of_pseudo\|weakly\|of_sigma\|exists_isOpen'`
- `rg -n "theorem le_iff\b|theorem le_iff'|theorem Monotone.measure_iUnion|theorem measure_inter_add_sdiff|theorem restrict_apply'|theorem isFiniteMeasure_restrict" mathlib/Mathlib/MeasureTheory -g '*.lean'; rg -n 'Monotone.measure_iUnion' mathlib/Mathlib/MeasureTheory; rg -n 'isFiniteMeasure_restrict' mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `rg -n 'theorem infEDist_pos_iff_notMem_closure|theorem continuous_infEDist|theorem infEDist_zero_of_mem' mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean; rg -n 'exists_iUnion_isClosed' mathlib/Mathlib; rg -n 'theorem exists_inv_nat_lt' mathlib/Mathlib; rg -n 'theorem isCompact_of_isClosed_isBounded' mathlib/Mathlib`
- `rg -n 'IMRep|measure_le_of|le_on_open|massOn_le_add' project/GMT -g '*.lean'`
- `rg -n 'theorem le_massOn|def massOn|def massAdmissibleOn|theorem covectorEuclideanNorm_neg' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean; rg -n -i 'outer.?regular|OuterRegular' simongmt/Poincare -g '*.lean'; #eval env.header.moduleNames.contains `Poincare.SimonGMT.Chapter01.ExactRegularity after import GMT.Ch07.Submission (false)`
- `python3 -I scans of dag.json lean_statement/lean_name/status: measure inequalities, IMRep weight facts (R.measure Uᶜ / R.measure K), open-to-Borel extension lemmas, mass triangle; lean_name lookups of lcmp_massOn_le_add_of_eval_eq, dtc_mass_eq_measure, cbr_imRep_measure_basic, rsd_imrep_compact_measure_ne_top, cmc_ml_measure_eq_of_eq_on_open_subsets, lcmp_measure_le_add_of_open_nhds`
- `git grep -n 'theorem Submission.<name> ' <candidate> -- GMT for c7dea4b8 (lcmp_massOn_le_add_of_eval_eq), d37eb4df (cbr_imRep_measure_basic), bff81d31 (dtc_mass_eq_measure), 702e7082 (rsd_imrep_compact_measure_ne_top); git show <candidate>:GMT/Ch07/Submission.lean (accepted proofs)`
- `grep -c dtc_bc_lc_measure_le_of_le_on_open dag.json issue-workers.json DAG.md; grep -rl over GMT, .lake/packages/simongmt and the snapshot project; git grep -l over the 1832 distinct ref commits -- GMT (no match)`
- `sed of runtime.py (_existing_lean_name_problem, _accepted_checkpoint, _solve_children, _install_parent_supplied_child_handoff, _overlay_accepted_children) and store.py ensure; grep -n 'def contract_scope|def child_modules' verifier/gmt-compare.py`
- `lake env lean /tmp/msub_split/{Names,NewChild,NewChildFinal,Assembly,AssemblyFromJson,Full,Solutions,Closure}.lean and /tmp/msub_split/challenges/Challenge_<key>.lean (generated by gmt-compare.py child_modules, contract mode); python3 -I /tmp/msub_split/scripts/{children,build}.py (lean_contract.validate_lean_statement, schema and identity checks)`
- `sed -n 268,300p book/chapter-01.txt (Simon Theorem 1.15); sed -n 755,770p book/chapter-06.txt (Simon 6.3.2(3)); grep -n '2.5 Remarks' book/chapter-07.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/CompleteLattice.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/ExactRegularity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-9a7649a7ed/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-mass-triangle-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-mass-eq-measure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6249c06eba/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-imrep-local-finiteness-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/msub_split/NewChildFinal.lean`
- `/tmp/msub_split/Assembly.lean`
- `/tmp/msub_split/AssemblyFromJson.lean`
- `/tmp/msub_split/Full.lean`
- `/tmp/msub_split/Solutions.lean`
- `/tmp/msub_split/challenges/Challenge_open_to_borel.lean`
- `/tmp/msub_split/out/subproblems.json`

The snapshot (project b4d606db, Mathlib 25730c7c) Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Its project has only the IMRep definitions and no measure-comparison lemma (rg no match for measure_le_of / le_on_open / massOn_le_add).

Every Mathlib fact the new child needs exists in the snapshot and was exercised in a compiled proof:
- Set.exists_isOpen_lt_of_lt and the instance WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure (WeaklyRegular extends OuterRegular) in Regular.lean:359/1072/324;
- Measure.le_iff in CompleteLattice.lean:41; Monotone.measure_iUnion in Continuity.lean:71; measure_inter_add_sdiff in Basic.lean:83; Measure.restrict_apply' in Restrict.lean:111; isFiniteMeasure_restrict in Typeclasses/Finite.lean:40;
- Metric.continuous_infEDist, infEDist_zero_of_mem and infEDist_pos_iff_notMem_closure in HausdorffDistance.lean:140/107/174;
- ENNReal.exists_inv_nat_lt in Basic/ENNReal/Inv.lean:650; isCompact_of_isClosed_isBounded in Bounded.lean:320.

SimonGMT Chapter06/Mass.lean supplies massOn, massAdmissibleOn, le_massOn and covectorEuclideanNorm_neg, which the reused mass triangle uses. SimonGMT's only outer-regularity result is Chapter01/ExactRegularity.lean weaklyRegular_of_closedSetsAreGDelta_of_open_cover. It needs a finite open cover of the whole space and is not in the contract's import closure, so it is not usable.

Three obligations are comparator-accepted DAG declarations with identical frozen types and are reused: lcmp_massOn_le_add_of_eval_eq, dtc_mass_eq_measure and cbr_imRep_measure_basic. No existing declaration extends an inequality between measures from open subsets of U to all sets:
- cmc_ml_measure_eq_of_eq_on_open_subsets proves only equality;
- lcmp_measure_le_add_of_open_nhds covers only compact E.
That extension is the new child dtc_bc_lc_measure_le_of_le_on_open, whose name is globally unused.

All four child types elaborate in the comparator scope, and the new child is fully proved in Lean. The exact parent type follows from the four child types by a hypothesis-only assembly. Only propext, Classical.choice and Quot.sound are used.
