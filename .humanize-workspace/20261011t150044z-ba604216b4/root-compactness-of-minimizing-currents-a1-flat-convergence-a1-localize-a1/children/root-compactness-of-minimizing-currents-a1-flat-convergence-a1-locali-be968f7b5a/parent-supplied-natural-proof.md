# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1.mass_le_measure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the mass estimates of steps 0 and 8 of the parent proof of cmc_fc_localize. These rest on (R3): if |ω| ≤ 1, then ∫_B⟨ω, ξ⟩ dμ ≤ μ(B). Here the estimate is stated for an arbitrary integral current and an arbitrary region V. The parent uses it with X = A_{φ(j)}(s), E = {g < s}, V = U (M(T'_j) ≤ μ_{φ(j)}({g < s})), with X = B_{φ(j)}(s) (M(B) ≤ μ'_{φ(j)}({g < s})), and with μ = 0 for the zero current in step 0. The integral is the Bochner integral, which is 0 for non-integrable integrands, so no finiteness or integrability assumption is needed.
1. By definition, M_V(X) is the supremum of ENNReal.ofReal(X(ω)) over the admissible ω: those ω ∈ 𝒟^d(U) with tsupport ω ⊆ V and |ω(x)| ≤ 1 for all x (massAdmissibleOn U d V). Fix such an ω. It suffices (sSup_le) to show ENNReal.ofReal(X(ω)) ≤ μ(E ∩ V).
2. Put f(x) := ξ(x)(ω(x)) and S := tsupport ω, a closed (hence Borel) set with S ⊆ V. Then ENNReal.ofReal(X(ω)) = ENNReal.ofReal(∫_E f dμ) ≤ ENNReal.ofReal|∫_E f dμ| = ‖∫_E f dμ‖ₑ (Real.enorm_eq_ofReal_abs) ≤ ∫⁻_E ‖f‖ₑ dμ. The last inequality is Mathlib enorm_integral_le_lintegral_enorm, which holds for every f.
3. Claim: ‖f(x)‖ₑ ≤ 1_S(x) for μ⌞E-a.e. x. The hypothesis holds μ-a.e., hence μ⌞E-a.e. (ae_restrict_of_ae). If x ∈ S, then ‖f(x)‖ₑ = ENNReal.ofReal|ξ(x)(ω(x))| ≤ ENNReal.ofReal|ω(x)| ≤ ENNReal.ofReal 1 = 1, by the hypothesis with α := ω(x) and by admissibility. If x ∉ S, then ω(x) = 0 (image_eq_zero_of_notMem_tsupport), so f(x) = ξ(x)(0) = 0.
4. By lintegral_mono_ae, ∫⁻_E ‖f‖ₑ dμ ≤ ∫⁻_E 1_S dμ = (μ⌞E)(S) = μ(S ∩ E), using lintegral_indicator_one and Measure.restrict_apply (S Borel). Since S ⊆ V, μ(S ∩ E) ≤ μ(E ∩ V) (measure_mono).
5. Combining steps 2-4, ENNReal.ofReal(X(ω)) ≤ μ(E ∩ V) for every admissible ω. Hence M_V(X) ≤ μ(E ∩ V). ∎
Appendix (verified Lean). This tactic proof of exactly the frozen statement compiled after import GMT.Ch07.Submission inside namespace GMT.Ch07 with the contract's opens. #print axioms: propext, Classical.choice, Quot.sound.
  intro P d U X μ ξ E V hξ hX
  apply sSup_le
  rintro r ⟨ω, hω, rfl⟩
  show ENNReal.ofReal (X ω) ≤ _
  rw [hX ω]
  have hS : MeasurableSet (tsupport (ω : DifferentialForm (Euclid P) d)) :=
    (isClosed_tsupport _).measurableSet
  calc ENNReal.ofReal (∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) d) x) ∂μ)
        ≤ ‖∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) d) x) ∂μ‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ x in E, ‖ξ x ((ω : DifferentialForm (Euclid P) d) x)‖ₑ ∂μ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x in E, (tsupport (ω : DifferentialForm (Euclid P) d)).indicator 1 x ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae hξ] with x hx
        by_cases hxs : x ∈ tsupport (ω : DifferentialForm (Euclid P) d)
        · rw [indicator_of_mem hxs, Pi.one_apply, Real.enorm_eq_ofReal_abs]
          calc ENNReal.ofReal |ξ x ((ω : DifferentialForm (Euclid P) d) x)|
              ≤ ENNReal.ofReal (covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) d) x)) :=
                ENNReal.ofReal_le_ofReal (hx _)
            _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (hω.2 x)
            _ = 1 := ENNReal.ofReal_one
        · rw [indicator_of_notMem hxs]
          have h0 : (ω : DifferentialForm (Euclid P) d) x = 0 := image_eq_zero_of_notMem_tsupport hxs
          simp [h0]
    _ = μ.restrict E (tsupport (ω : DifferentialForm (Euclid P) d)) := lintegral_indicator_one hS
    _ = μ (tsupport (ω : DifferentialForm (Euclid P) d) ∩ E) := Measure.restrict_apply hS
    _ ≤ μ (E ∩ V) := measure_mono (fun x hx => ⟨hx.2, hω.1 hx.1⟩)

## Key steps

1. Reduce to one admissible ω: ofReal(X ω) = ofReal(∫_E⟨ω,ξ⟩dμ) ≤ ‖∫_E⟨ω,ξ⟩dμ‖ₑ ≤ ∫⁻_E ‖⟨ω,ξ⟩‖ₑ dμ.
2. a.e. on E, ‖⟨ω,ξ⟩‖ₑ ≤ 1_{tsupport ω}: the unit bound and |ω| ≤ 1 hold on the support, and ω = 0 off it.
3. ∫⁻_E 1_{tsupport ω} dμ = μ(tsupport ω ∩ E) ≤ μ(E ∩ V); then take the supremum over ω.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `rg -n 'cmc_fcl|cmc_fc_localize|weakConverges_sublevel' local-references/123e8435b4a2469b/project --glob '*.lean' (no match)`
- `rg -n 'theorem integral_withDensity_eq_integral_smul |theorem exists_contMDiffMap_one_nhds_of_subset_interior|theorem _root_.IsCompact.exists_cthickening_subset_open|theorem tendsto_measure_iInter_atTop|theorem norm_setIntegral_le_of_norm_le_const_ae|theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|theorem enorm_integral_le_lintegral_enorm|theorem restrict_withDensity|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem lipschitz_infDist_pt|theorem _root_.IsCompact.cthickening' local-references/123e8435b4a2469b/mathlib/Mathlib --glob '*.lean'`
- `grep -rn 'GeometricCurrentOn.support|def GeometricCurrentOn.zeroRegion|GeometricCurrentOn.VanishesOn|restrictDomain' lake-packages-25730c7c/simongmt/Poincare/SimonGMT; cat Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean`
- `python3 over dag.json: statuses and frozen types of the flat_convergence siblings (cmc_fc_good_slice); accepted declarations mentioning IMRep/massOn/support (dor_ims_action_eq_integral, dor_ims_massOn_le_measure, rsd_cmr_support_subset_of_vanish, rsd_mw_wlm_eval_eq_integral_restrict); lcmp_massOn_le_add_of_eval_eq (decomposing under another parent); collision check of the cmc_fcl_* names (none)`
- `sed /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py (_existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff, _overlay_accepted_children, decomposition workspace publication) and store.py ensure`
- `sed -n 2028,2110p book/chapter-06.txt (Simon 7.2; localization sentence at lines 2090-2096)`
- `lake env lean /tmp/lczdec/T1.lean, /tmp/lczdec/check/T2.lean (#check probes of the GMT.Ch07.Submission import closure; smooth Urysohn cutoff via exists_contMDiffMap_one_nhds_of_subset_interior), /tmp/lczdec/check/T6.lean-T8.lean (elaboration-time probes)`
- `lake env lean /tmp/lczdec/Assembly.lean (child stubs, cmc_fc_good_slice stub and the assembly of the exact cmc_fc_localize type: no errors)`
- `lake env lean /tmp/lczdec/Full.lean (six child proofs plus the assembly; #print axioms of the children: propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-localize-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-localize-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/store.py`
- `/tmp/lczdec/Assembly.lean`
- `/tmp/lczdec/Full.lean`

The snapshot is project b4d606db with Mathlib 25730c7c. Its Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. The snapshot contains no cmc_fcl_* or cmc_fc_localize declaration (rg: no match). SimonGMT Chapter06 supplies massOn, mass, support, zeroRegion, massOn_mono and le_massOn, but none of the seven child facts. The pinned Mathlib supplies every tool the compiled child proofs use, all inside the import closure of GMT.Ch07.Submission: integral_withDensity_eq_integral_smul, restrict_withDensity, Measure.restrict_restrict, withDensity_absolutelyContinuous, IsCompact.exists_cthickening_subset_open, IsCompact.cthickening, lipschitz_infDist_pt, enorm_integral_le_lintegral_enorm, setIntegral_eq_integral_of_forall_compl_eq_zero, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, norm_setIntegral_le_of_norm_le_const_ae, Measure.integrableOn_of_bounded, tendsto_measure_iInter_atTop, exists_contMDiffMap_one_nhds_of_subset_interior and contMDiff_iff_contDiff. Among accepted DAG declarations, rsd_cmr_support_subset_of_vanish is reused with its identical frozen type. lcmp_massOn_le_add_of_eval_eq is still active under another parent, so it is not shared and cmc_fcl_massOn_le_add is introduced instead. No cmc_fcl_* name collides with any of the 668 DAG names. All seven child types elaborate. The exact frozen type of cmc_fc_localize compiles from the seven children and cmc_fc_good_slice. The six new children compile using only the axioms propext, Classical.choice and Quot.sound.
