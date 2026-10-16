# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.index_comparison-a1.region_bound-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.index_comparison-a1.region_bound-a1.compact_sum_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the selected parent's proof (region Σ = F ∖ W; parent 8(c)). There the open set is U′ = U ∖ spt(S − C), the compact set is Σ and Y is Ŷ. Here they are an arbitrary open U′ ⊆ U, a compact E ⊆ U′ and any represented Y. This is Simon 7.2.4 (10) (chapter-07.txt lines 245–256): an inequality between masses on open neighbourhoods is passed to the limit set by letting the neighbourhoods shrink. Siblings used: (MR) mass_and_support, part (i): if R′ represents a current A in an open domain, then M_G(A) = μ_{R′}(G) for every open G ⊆ ℝ^P. (COB) compact_outer_bound. (FIN) imrep_local_finiteness, second conjunct: μ_{R′}(K) ≠ ∞ for every IMRep R′ in a set V and every compact K ⊆ V. (MT) mixed_mass_triangle.
Notation. μ_R = R.measure, μ_{R_Z} = R_Z.measure and μ_{R_Y} = R_Y.measure are measures on ℝ^P. For ω ∈ 𝒟ⁿ(U), ιω = testFormOnInclusion (U ⊆ ℝ^P) n ω and ι₀ω := testFormOnInclusion (U ⊆ U) n ω.
1. (Masses on open sets.) U and ℝ^P are open. By (MR)(i) for (T, R) and (Z, R_Z) in U and for (Y, R_Y) in ℝ^P, every open G ⊆ ℝ^P satisfies M_G(T) = μ_R(G), M_G(Z) = μ_{R_Z}(G) and M_G(Y) = μ_{R_Y}(G).
2. (Local finiteness.) Let ν := μ_R + μ_{R_Y}, a measure on ℝ^P with ν(A) = μ_R(A) + μ_{R_Y}(A) for all A (Measure.add_apply). Let K ⊆ U′ be compact. Then K ⊆ U because U′ ⊆ U, so μ_R(K) ≠ ∞ by (FIN) for the IMRep R in U. Also K ⊆ ℝ^P, so μ_{R_Y}(K) ≠ ∞ by (FIN) for the IMRep R_Y in ℝ^P. Hence ν(K) < ∞ (ENNReal.add_lt_top).
3. (The identity on a neighbourhood.) Let G be open with E ⊆ G and CompactlyContained G U′, i.e. closure(G) is compact and closure(G) ⊆ U′. Then G ⊆ closure(G) ⊆ U′. Let ω ∈ 𝒟ⁿ(U) with tsupport ω ⊆ G. Then tsupport ω ⊆ U′, so by hypothesis Z(ω) = T(ω) + Y(ιω). Now ι₀ω has the same underlying form as ω and lies in the same space 𝒟ⁿ(U); elements of 𝒟ⁿ(U) are determined by their underlying form, so ι₀ω = ω. Hence Z(ω) = T(ι₀ω) + 1·Y(ιω).
4. (Bound on the neighbourhood.) Apply (MT) with the domains U ⊆ V₁ := U and U ⊆ V₂ := ℝ^P, the currents Z, X := T and Y, and c := 1. Its hypothesis is step 3. Since ofReal(|1|) = 1, it gives M_G(Z) ≤ M_G(T) + M_G(Y). G is open, so step 1 turns this into μ_{R_Z}(G) ≤ μ_R(G) + μ_{R_Y}(G) = ν(G) + 0.
5. (Passage to E.) Apply (COB) with the open set U′, the compact set E ⊆ U′, the measures μ := μ_{R_Z} and ν, and the constant c := 0. Its finiteness hypothesis is step 2 and its neighbourhood hypothesis is step 4. It gives μ_{R_Z}(E) ≤ ν(E) + 0 = μ_R(E) + μ_{R_Y}(E). ∎
Appendix (verified Lean realization of the numbered proof above; not part of the proof). The declaration below compiles with Lean v4.35.0-rc3, Mathlib 25730c7c and SimonGMT 2b366308 in the child comparator scope (after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the frozen contract's `open` commands, after its `noncomputable section ... end`), once the four sibling declarations Submission.dor_imrep_massOn_eq_measure_and_support, Submission.lcmp_measure_le_add_of_open_nhds, Submission.rsd_imrep_compact_measure_ne_top and Submission.dimred_mbl_lc_ic_rb_massOn_le_add_incl are present. It was compiled together with the real accepted proofs of the three reused siblings (candidate commits d49dda91, bb7f0a56 and 702e7082) and the proof of dimred_mbl_lc_ic_rb_massOn_le_add_incl above; `#print axioms` reports only propext, Classical.choice and Quot.sound.
```lean
theorem Submission.dimred_mbl_lc_ic_rb_measure_le_add_of_compact : ∀ (P n : ℕ) (U U' E : Set (Euclid P)) (T Z : GeometricCurrentOn U n) (Y : GeometricCurrentOn (univ : Set (Euclid P)) n) (R RZ : IMRep U n) (RY : IMRep (univ : Set (Euclid P)) n), IsOpen U → IsOpen U' → U' ⊆ U → IsCompact E → E ⊆ U' → R.Represents T → RZ.Represents Z → RY.Represents Y → (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ U' → Z ω = T ω + Y (testFormOnInclusion (subset_univ U) n ω)) → RZ.measure E ≤ R.measure E + RY.measure E := by
  intro P n U U' E T Z Y R RZ RY hU hU' hU'U hE hEU' hR hRZ hRY hZ
  have hMT := (Submission.dor_imrep_massOn_eq_measure_and_support P n U T R hU hR).1
  have hMZ := (Submission.dor_imrep_massOn_eq_measure_and_support P n U Z RZ hU hRZ).1
  have hMY := (Submission.dor_imrep_massOn_eq_measure_and_support P n univ Y RY isOpen_univ hRY).1
  have key := Submission.lcmp_measure_le_add_of_open_nhds P U' E RZ.measure
    (R.measure + RY.measure) 0 hU' hE hEU' ?_ ?_
  · simpa [Measure.add_apply] using key
  · intro K hK hKU'
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.2
      ⟨lt_top_iff_ne_top.2 (Submission.rsd_imrep_compact_measure_ne_top P n U R K hK (hKU'.trans hU'U)).2,
        lt_top_iff_ne_top.2 (Submission.rsd_imrep_compact_measure_ne_top P n univ RY K hK (subset_univ K)).2⟩
  · intro G hG hEG hGU'
    have hGU' : G ⊆ U' := subset_closure.trans hGU'.2
    have htri := Submission.dimred_mbl_lc_ic_rb_massOn_le_add_incl P n U U univ G (subset_refl U)
      (subset_univ U) Z T Y 1 (fun ω hω => by
        rw [hZ ω (hω.trans hGU'), one_mul]; rfl)
    rw [hMZ G hG, hMT G hG, hMY G hG] at htri
    simpa [Measure.add_apply] using htri
```

## Key steps

1. mass_and_support (i): M_G(T) = μ_R(G), M_G(Z) = μ_{R_Z}(G) and M_G(Y) = μ_{R_Y}(G) for every open G.
2. ν := μ_R + μ_{R_Y} is finite on compact subsets of U′, by imrep_local_finiteness applied in U (K ⊆ U′ ⊆ U) and in ℝ^P.
3. For open G ⊇ E with CompactlyContained G U′ we have G ⊆ U′, so Z(ω) = T(ω) + 1·Y(ιω) for forms supported in G; mixed_mass_triangle with c = 1 and mass_and_support give μ_{R_Z}(G) ≤ ν(G) + 0.
4. compact_outer_bound with U′, E, μ_{R_Z}, ν and c = 0 gives μ_{R_Z}(E) ≤ μ_R(E) + μ_{R_Y}(E).

## Reference use

### local-project

Queries:
- `cat RUN/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-b3446f1e5e/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `cat RUN/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD (b4d606db1); cmp snapshot project/GMT/Ch07/Contract.lean with GMT/Ch07/Contract.lean and GMT/Ch07/Submission.lean (identical)`
- `python3 over RUN/dag.json: selected node (depth 5, decomposing), parent index_comparison-a1 and its six children, the three resolved dependencies; depth histogram (max depth 6); accepted nodes whose lean_statement mentions massOn with testFormOnInclusion, currentEval, or '.measure K ≠ ∞|< ∞' (found lcmp_massOn_le_add_of_eval_eq, dtc_massOn_eq_of_agreeOn, cmc_ml_massOn_eq_of_disjoint_sub_support, rsd_cmr_massOn_eq_ofReal_mul, rsd_imrep_compact_measure_ne_top, cbr_imRep_measure_basic, cmc_fcl_imrep_integral_data; no mixed-domain mass triangle and no compact-set mass-measure comparison)`
- `python3 over RUN/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-32e3afa931/decomposition-v1.json and RUN/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-imrep-local-finiteness-a1/parent-child-handoff.json (audited texts of the four reused declarations)`
- `grep -n 'node.depth >= self.config.max_depth|_existing_lean_name_problem|_accepted_checkpoint|_overlay_accepted_children' /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py; sed -n 200,330p prompts.py (DECOMPOSE, DECOMPOSITION_AUDIT, RLCR_LEAN_TASK)`
- `python3 -I: verifier/gmt-compare.py contract_scope(GMT/Ch07/Contract.lean, GMT.Ch07.main_theorem) (replay: open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (...); noncomputable section; end)`
- `sed/grep in lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Mass,Currents,CurrentLocalEquality}.lean: covectorEuclideanNorm_neg, massAdmissibleOn, massOn, mass, massOn_mono, le_massOn, TestFormOn, GeometricCurrentOn, zero_apply, testFormOnInclusion(_coe), restrictDomain_apply, zeroRegion, support, isOpen_zeroRegion`
- `grep -n currentEval GMT/Ch07/Contract.lean (definition at lines 153–155: if IsTestForm ω ∧ tsupport ω ⊆ U then T ⟨ω, h⟩ else 0)`
- `rg -n 'theorem measure_inter_add_sdiff|theorem ofReal_add_le|theorem ofReal_mul|theorem add_lt_top|theorem IsCompact.diff|theorem IsClosed.sdiff|theorem IsOpen.sdiff' RUN/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `sed -n 160,262p book/chapter-07.txt (Simon 7.2.4 proof (1)–(12))`
- `name collision scan: grep dimred_mbl_lc_ic_rb_ in RUN/dag.json, DAG.md, issue-workers.json, RUN/nodes, RUN/decomposition-reopenings, GMT/, .lake/packages/simongmt, snapshot project; git grep over all 4145 distinct ref commits -- GMT (no match)`
- `git diff -U0 b4d606db1 <44ef61f7|d49dda91|bb7f0a56|702e7082> -- GMT/Ch07/Submission.lean (single inserted hunk each; extracted into /tmp/rb_dec_scratch/reused_blocks.lean)`
- `lake env lean /tmp/rb_dec_scratch/Check1.lean (mixed_mass_triangle proof; compact_sum_bound conditional on the frozen types of mass_and_support, compact_outer_bound, imrep_local_finiteness, mixed_mass_triangle)`
- `lake env lean /tmp/rb_dec_scratch/Check2.lean (exact frozen parent type conditional on vanish_off_support, mass_and_support, mixed_mass_triangle, compact_sum_bound; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/rb_dec_scratch/Final.lean (Submission.X layout and comparator-style _root_.HumanizeNodeComparator.targetN : (type) := by exact Submission.X for all seven types)`
- `lake env lean /tmp/rb_dec_scratch/E2E.lean (real accepted proofs of the four reused declarations + both new children + the parent; exit 0, no errors; #print axioms: propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-b3446f1e5e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-b3446f1e5e/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-b3446f1e5e/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-32e3afa931/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-imrep-local-finiteness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-imrep-local-finiteness-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-mass-triangle-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/rb_dec_scratch/Check1.lean`
- `/tmp/rb_dec_scratch/Check2.lean`
- `/tmp/rb_dec_scratch/Final.lean`
- `/tmp/rb_dec_scratch/reused_blocks.lean`
- `/tmp/rb_dec_scratch/E2E.lean`

The pins match the manifest: project b4d606db1, Mathlib 25730c7c, SimonGMT 2b366308. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical. Neither the pinned libraries nor the accepted DAG nodes state either new child. The accepted lcmp_massOn_le_add_of_eval_eq is the same-domain triangle with |c| ≤ 1. dtc_massOn_eq_of_agreeOn compares masses under restriction. Neither handles Z on U against currents on ℝ^P with an arbitrary coefficient. No accepted declaration passes a mass-measure inequality from Z = T + Y|_U to a compact set. Four accepted declarations are reused with byte-identical types: dtc_vanish_off_support, dor_imrep_massOn_eq_measure_and_support, lcmp_measure_le_add_of_open_nhds and rsd_imrep_compact_measure_ne_top. SimonGMT provides massOn, massAdmissibleOn, le_massOn, massOn_mono, covectorEuclideanNorm_neg, testFormOnInclusion_coe, support and isOpen_zeroRegion. The snapshot Mathlib provides measure_inter_add_sdiff, ENNReal.ofReal_add_le, ENNReal.ofReal_mul, ENNReal.add_lt_top, IsCompact.diff and IsOpen.sdiff/IsClosed.sdiff. Lean checks: all child types elaborate in the comparator scope. Both new children are proved, and the exact frozen parent type is proved from the six children. This holds with the real accepted proofs of the reused declarations, using only propext, Classical.choice and Quot.sound. The new names are unused everywhere.
