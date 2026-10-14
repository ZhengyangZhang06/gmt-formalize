# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.closure_compact-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.closure_compact-a1.filling-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the supplied proof (parent V3), and Simon Ch. 6, proof of 8.2 (book/chapter-06.txt lines 2322–2337: "the general case of the theorem follows from the special case when ∂T = 0"). It is stated for one current T with compact support and IM boundary of finite mass. For n = d + 1 ≥ 2 it uses (Isor) with m := d − 1, which is in range because m + 1 = d < P. For n = 1 it is the segment construction. Deviation from the supplied proof: the base point is 0 instead of a point x₀ ∉ {x_i}; a point x = 0 then contributes the zero segment current, which segment_current allows (a = b). Siblings used: support_vanish (rsd_cmr_support_subset_of_vanish), current_algebra (cbr_cc_current_algebra) part (c), segment_current (dmcbr_cc_segment_current) and zero_current_sum (dmcbr_cc_zero_current_finite_sum). Notation: M := M_{ℝ^P}; for a 0-form g, g(x)⟨⟩ is the value of the 0-covector g(x) on the empty tuple; dη := exteriorDerivativeTestOn ℝ^P applied to η, so ∂S(η) = S(dη).
1. spt ∂T ⊆ spt T, and spt ∂T is compact. Let η be a test d-form whose tsupport is disjoint from spt T. Since tsupport dη ⊆ tsupport η (tsupport_exteriorDerivative_subset), tsupport dη is disjoint from spt T too. So ∂T(η) = T(dη) = 0 by (VO). Apply support_vanish with U := ℝ^P (open), K := spt T (compact) and F := ∂T. It gives spt ∂T ⊆ spt T, and spt ∂T is compact.
Case d = m + 1 (n ≥ 2).
2. Filling of the cycle. Z := ∂T ∈ 𝒟_{m+1}(ℝ^P) is IM, has compact support (step 1) and finite mass, and ∂Z = ∂∂T = 0 (GeometricCurrentOn.boundary_boundary). Since m + 1 = d < P, (Isor) with (P, m) gives a constant c ≥ 1. Its conclusion for Z gives an IM Y ∈ 𝒟_{m+2}(ℝ^P) = 𝒟_{d+1}(ℝ^P) with ∂Y = Z = ∂T, M(Y) ≤ ENNReal.ofReal(c(2cM(Z))^{1/(m+1)}M(Z)) < ∞ and spt Y ⊆ thickening_r(spt Z), where r := 3√P(2cM(Z))^{1/(m+1)}.
3. spt Y is compact. spt Z is compact, hence bounded. So its r-thickening is bounded (Bornology.IsBounded.thickening), and its closure C is compact, because ℝ^P is proper. Let ω be a test form whose tsupport is disjoint from C. Then it is disjoint from spt Y ⊆ thickening_r(spt Z) ⊆ C, so Y(ω) = 0 by (VO). Applying support_vanish with K := C shows that spt Y is compact. So Y is as required.
Case d = 0 (n = 1).
4. Point-mass form. ∂T ∈ 𝒟_0(ℝ^P) is IM with compact support (step 1). zero_current_sum (with (MR) and (VO)) gives a finite set F ⊆ spt ∂T ⊆ spt T and integers m(x) with ∂T(g) = Σ_{x∈F} m(x)·g(x)⟨⟩ for every test 0-form g.
5. Total multiplicity zero. spt T is compact, so spt T ⊆ B_ρ(0) for some ρ > 0. Let ψ be a smooth bump function with ψ = 1 on B̄_ρ(0) and support in B_{2ρ}(0) (ContDiffBump with radii ρ < 2ρ). Let g be the test 0-form g(y) := constOfIsEmpty(ψ(y)), so g(y)⟨⟩ = ψ(y). It is smooth and compactly supported.
 For y ∈ B_ρ(0), ψ = 1 on a neighbourhood of y, so Dψ(y) = 0 and dg(y) = 0 (extDeriv_constOfIsEmpty). Hence tsupport dg lies in the closed set ℝ^P ∖ B_ρ(0), which contains {dg ≠ 0} and is disjoint from spt T ⊆ B_ρ(0). So ∂T(g) = T(dg) = 0 by (VO).
 On the other hand, F ⊆ spt T ⊆ B_ρ(0), where ψ = 1, so ∂T(g) = Σ_{x∈F} m(x)ψ(x) = Σ_{x∈F} m(x). Therefore Σ_{x∈F} m(x) = 0.
6. Segments. For each x ∈ ℝ^P, segment_current (with (MR), a := 0, b := x) gives an IM S_x ∈ 𝒟_1(ℝ^P) with ∂S_x(g) = g(x)⟨⟩ − g(0)⟨⟩ for every test 0-form g, M(S_x) < ∞ and spt S_x ⊆ [0, x].
7. The filling. Apply current_algebra (c) with (IMC)(c), U := ℝ^P, ι := ℝ^P, the finite set F, the currents S_x and the integers m(x). It gives an IM Y ∈ 𝒟_1(ℝ^P) with Y(ω) = Σ_{x∈F} m(x)S_x(ω) for every ω, and M_W(Y) ≤ Σ_{x∈F} |m(x)|M_W(S_x) for every W.
8. ∂Y = ∂T. For a test 0-form η, using steps 6, 5 and 4:
 ∂Y(η) = Y(dη) = Σ_{x∈F} m(x)S_x(dη) = Σ_{x∈F} m(x)(η(x)⟨⟩ − η(0)⟨⟩) = Σ_{x∈F} m(x)η(x)⟨⟩ − (Σ_{x∈F} m(x))η(0)⟨⟩ = Σ_{x∈F} m(x)η(x)⟨⟩ = ∂T(η).
 So ∂Y = ∂T (GeometricCurrentOn.ext).
9. Finite mass. M(Y) ≤ Σ_{x∈F}|m(x)|M(S_x) < ∞, a finite sum of finite terms.
10. spt Y is compact. C := ⋃_{x∈F}[0, x] is compact: it is a finite union of segments, each the image of [0, 1] under the continuous map s ↦ s·x. Let ω be a test form whose tsupport is disjoint from C. For each x ∈ F, tsupport ω is then disjoint from spt S_x ⊆ [0, x], so S_x(ω) = 0 by (VO); hence Y(ω) = 0. Applying support_vanish with K := C shows that spt Y is compact. ∎
Appendix (verified Lean). This tactic proof of exactly the frozen statement compiled with lake env lean after import GMT.Ch07.Submission inside namespace GMT.Ch07 with the contract's opens, with the sibling declarations Submission.cbr_cc_current_algebra, Submission.rsd_cmr_support_subset_of_vanish, Submission.dmcbr_cc_segment_current, Submission.dmcbr_cc_zero_current_finite_sum available at their frozen types; #print axioms: propext, Classical.choice, Quot.sound and those sibling declarations.
  intro hMR hIMC hVO hISO P d hdP T hTc hbm hbim
  -- Step 1: `spt ∂T ⊆ spt T`, and `spt ∂T` is compact
  obtain ⟨hbsub, hbc⟩ := Submission.rsd_cmr_support_subset_of_vanish P d univ T.support
    T.boundary isOpen_univ hTc (subset_univ _) fun η hη => by
      rw [GeometricCurrentOn.boundary_apply]
      exact hVO P (d + 1) univ T (exteriorDerivativeTestOn univ d η) (Disjoint.mono_left
        (tsupport_exteriorDerivative_subset (η : DifferentialForm (Euclid P) d)) hη)
  rcases d with _ | m
  · -- Case `d = 0`.  Step 4: `∂T = Σ_{x ∈ F} m(x) δ_x`
    obtain ⟨F, m, hF, hsum⟩ :=
      Submission.dmcbr_cc_zero_current_finite_sum hMR hVO P T.boundary hbim hbc
    have hFT : ∀ x ∈ F, x ∈ T.support := fun x hx => hbsub (hF hx)
    -- Step 5: `Σ_{x ∈ F} m(x) = 0`, testing `∂T` on a bump `0`-form `≡ 1` near `spt T`
    obtain ⟨ρ, hρ, hTρ⟩ := hTc.isBounded.subset_ball_lt 0 (0 : Euclid P)
    let ψ : ContDiffBump (0 : Euclid P) := ⟨ρ, 2 * ρ, hρ, by linarith⟩
    let gf : DifferentialForm (Euclid P) 0 := fun y =>
      ContinuousAlternatingMap.constOfIsEmpty ℝ (Euclid P) (Fin 0) (ψ y)
    have hg : IsTestForm gf ∧ tsupport gf ⊆ univ :=
      ⟨⟨(ContinuousAlternatingMap.constOfIsEmptyLIE ℝ (Euclid P) ℝ (Fin 0)).contDiff.comp
          ψ.contDiff,
        ψ.hasCompactSupport.comp_left
          (map_zero (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ (Euclid P) ℝ (Fin 0)))⟩,
        subset_univ _⟩
    let g : TestFormOn (univ : Set (Euclid P)) 0 := ⟨gf, hg⟩
    have hdg : ∀ y ∈ ball (0 : Euclid P) ρ, exteriorDerivative gf y = 0 := by
      intro y hy
      have hψ : fderiv ℝ ψ y = 0 :=
        (ψ.eventuallyEq_one_of_mem_ball hy).fderiv_eq.trans (fderiv_const_apply 1)
      show extDeriv (fun x => ContinuousAlternatingMap.constOfIsEmpty ℝ (Euclid P) (Fin 0) (ψ x))
        y = 0
      rw [extDeriv_constOfIsEmpty, hψ]
      ext v
      simp
    have hTg : T.boundary g = 0 := by
      rw [GeometricCurrentOn.boundary_apply]
      refine hVO P (0 + 1) univ T (exteriorDerivativeTestOn univ 0 g)
        (Disjoint.mono ?_ hTρ disjoint_compl_left)
      exact closure_minimal (fun y hy hyρ => hy (hdg y hyρ)) isOpen_ball.isClosed_compl
    have htot : ∑ x ∈ F, (m x : ℝ) = 0 := by
      refine Eq.trans (Finset.sum_congr rfl fun x hx => ?_) ((hsum g).symm.trans hTg)
      show (m x : ℝ) = (m x : ℝ) * ψ x
      rw [ψ.one_of_mem_closedBall (ball_subset_closedBall (hTρ (hFT x hx))), mul_one]
    -- Step 6: segments `S_x` with `∂S_x = δ_x − δ_0` and `spt S_x ⊆ [0, x]`
    choose S hSim hSb hSm hSsupp using Submission.dmcbr_cc_segment_current hMR P (0 : Euclid P)
    -- Step 7: `Y = Σ_{x ∈ F} m(x) S_x` is integer multiplicity
    obtain ⟨Y, hYim, hYeval, hYmass⟩ :=
      Submission.cbr_cc_current_algebra.2.2 hIMC P 1 univ (Euclid P) F S m isOpen_univ
        fun x _ => hSim x
    refine ⟨Y, hYim, ?_, ?_, ?_⟩
    · -- Step 8: `∂Y = ∂T`
      ext η
      calc Y.boundary η
          = ∑ x ∈ F, (m x : ℝ) * S x (exteriorDerivativeTestOn univ 0 η) := by
            rw [GeometricCurrentOn.boundary_apply]
            exact hYeval (exteriorDerivativeTestOn univ 0 η)
        _ = ∑ x ∈ F, ((m x : ℝ) * (η : DifferentialForm (Euclid P) 0) x (fun i => i.elim0) -
              (m x : ℝ) * (η : DifferentialForm (Euclid P) 0) 0 (fun i => i.elim0)) :=
            Finset.sum_congr rfl fun x _ => by
              rw [← mul_sub, ← hSb x η, GeometricCurrentOn.boundary_apply]
        _ = ∑ x ∈ F, (m x : ℝ) * (η : DifferentialForm (Euclid P) 0) x (fun i => i.elim0) -
              (∑ x ∈ F, (m x : ℝ)) * (η : DifferentialForm (Euclid P) 0) 0 (fun i => i.elim0) := by
            rw [Finset.sum_sub_distrib, Finset.sum_mul]
        _ = T.boundary η := by rw [htot, zero_mul, sub_zero, hsum η]
    · -- Step 9: `M(Y) ≤ Σ_{x ∈ F} |m(x)| M(S_x) < ∞`
      exact (hYmass univ).trans_lt (ENNReal.sum_lt_top.2 fun x _ =>
        ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (hSm x))
    · -- Step 10: `Y` vanishes off the compact `⋃_{x ∈ F} [0, x]`
      have hC : IsCompact (⋃ x ∈ F, segment ℝ (0 : Euclid P) x) :=
        F.isCompact_biUnion fun x _ => by
          rw [segment_eq_image_lineMap]
          exact isCompact_Icc.image AffineMap.lineMap_continuous
      refine (Submission.rsd_cmr_support_subset_of_vanish P 1 univ _ Y isOpen_univ hC
        (subset_univ _) fun ω hω => ?_).2
      rw [hYeval ω]
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [hVO P 1 univ (S x) ω (hω.mono_right ((hSsupp x).trans
        (subset_iUnion₂ (s := fun x (_ : x ∈ F) => segment ℝ (0 : Euclid P) x) x hx))), mul_zero]
  · -- Case `d = m + 1`.  Step 2: fill the cycle `Z = ∂T` by (Isor) with `m + 1 < P`
    obtain ⟨c, -, hfill⟩ := hISO P m hdP
    obtain ⟨Y, hYim, hYb, hYm, hYsupp⟩ :=
      hfill T.boundary hbim hbc (GeometricCurrentOn.boundary_boundary T) hbm
    refine ⟨Y, hYim, hYb, hYm.trans_lt ENNReal.ofReal_lt_top, ?_⟩
    -- Step 3: `Y` vanishes off the compact closure of a bounded thickening of `spt Z`
    exact (Submission.rsd_cmr_support_subset_of_vanish P (m + 2) univ _ Y isOpen_univ
      hbc.isBounded.thickening.isCompact_closure (subset_univ _) fun ω hω =>
        hVO P (m + 2) univ Y ω (hω.mono_right (hYsupp.trans subset_closure))).2

## Key steps

1. spt ∂T ⊆ spt T is compact ((VO) for T, tsupport dη ⊆ tsupport η, support_vanish).
2. d = m + 1: (Isor) with m + 1 = d < P fills the cycle ∂T by an IM Y inside a bounded thickening of spt ∂T, so M(Y) < ∞ and spt Y is compact (support_vanish).
3. d = 0: ∂T = Σ_{x∈F} m(x)δ_x (zero_current_sum), and Σ m(x) = 0 by testing ∂T on a bump 0-form ≡ 1 near spt T and using (VO).
4. Y := Σ m(x)[[0, x]] (segment_current, current_algebra (c)) is IM with ∂Y = ∂T, M(Y) < ∞ and spt Y ⊆ ⋃[0, x] compact.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp GMT/Ch07/Contract.lean with the snapshot project/GMT/Ch07/Contract.lean (identical) and with GMT/Ch07/Submission.lean (identical)`
- `python3 -I scans of dag.json (2354 nodes): depth/status of the selected node (depth 5; max_depth 6); lean_name, status, candidate_commit and lean_statement of every cbr_cc_*, cbr_ccisp_*, dmcbr_cc_*, cmc_fcl_* node, rsd_cmr_support_subset_of_vanish, dtc_imrep_current, cmc_slice_mass_bounds, cbr_setIntegral_eq_of_integral_eq; one node per reused lean_name with byte-identical lean_statement; prefix scan dtc_bc_tc_cl_cc (no match)`
- `python3 -I reads of nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-e6c3d0d31e/decomposition-v2.json (frozen types of slicing, restrict_unique, foundations, slice_limit, lower_density, cycle_im), nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b218e818f5/decomposition-v1.json (cbr closure_compact split) and nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-326096d948/decomposition-v1.json (cbr isp_of_im split)`
- `git show c74800df52 (accepted Lean proof of dmcbr_cc_slice_property_of_im) and git show fbb6f2da14 (draft Lean proof of dmcbr_cc_compact_im_filling); git show <candidate>:GMT/Ch07/Submission.lean for 791f7d722e, 02c6122c94, b4a337bf47, ad94b18a1b, 21e4e0a22c, 1041782e1e, 3a4872b49a, 594767533a (Submission.* names used by the reused accepted proofs)`
- `rg -n "theorem liminf_le_of_frequently_le'|theorem Frequently.of_forall|theorem measurableSet_lt|theorem tendsto_nhds_unique|theorem IsCompact.union|theorem Finset.isCompact_biUnion|IsBounded.thickening|IsBounded.isCompact_closure|theorem extDeriv_constOfIsEmpty|theorem one_of_mem_closedBall|theorem eventuallyEq_one_of_mem_ball|theorem segment_eq_image_lineMap|theorem add_lt_top" local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'WeaklyConvergesOn.massOn_le_liminf|WeaklyConvergesOn.boundary|GeometricCurrentOn.boundary_boundary|GeometricCurrentOn.ext|boundary_apply|massOn_mono|tsupport_exteriorDerivative_subset|exteriorDerivativeTestOn|GeometricCurrentOn.support|isOpen_zeroRegion' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06`
- `rg -n 'dtc_bc_tc_cl_cc|cbr_cc_|dmcbr_cc_|cbr_ccisp_|cmc_fcl_|rsd_cmr_' local-references/123e8435b4a2469b/project (no match)`
- `lake env lean /tmp/ccdecomp_work/lean/Types.lean (10 child, 6 dependency and the node type elaborate), Assembly.lean (node type from the child and dependency types; axioms propext, Classical.choice, Quot.sound), Children.lean (isp_of_im and filling from their declared siblings; standard axioms), SubNames.lean (the same proofs against Submission.* names; #print axioms lists exactly the declared prerequisites)`
- `python3 -I verifier/lean_contract.py validate_lean_statement on all 10 child types (pass); verifier/gmt-compare.py contract_scope(Contract.lean, GMT.Ch07.main_theorem) for the replayed opens/namespace`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint|def ensure|_install_parent_supplied_child_handoff' /runtime/flows/gmt-claude-73516a26825a/_recursive_lean/{runtime,store}.py (reuse of accepted declarations by identical type; existing nodes are linked, not rewritten)`
- `grep -n 'special case|8.2|8.3' book/chapter-06.txt; sed -n 2300,2345p (Simon Ch. 6, 8.2–8.3: reduction to ∂T = 0)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-f30aba5c31/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-f30aba5c31/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-e6c3d0d31e/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b218e818f5/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b218e818f5/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-326096d948/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-253f25df92/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-8786a22a66/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-cc3788be20/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-40399ad363/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-locali-be968f7b5a/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-437b2394ee/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-dbf4768ac7/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convex/Segment.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-73516a26825a/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-73516a26825a/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/ccdecomp_work/lean/Types.lean`
- `/tmp/ccdecomp_work/lean/Assembly.lean`
- `/tmp/ccdecomp_work/lean/Children.lean`
- `/tmp/ccdecomp_work/lean/SubNames.lean`

The snapshot (local-project, project b4d606db, Mathlib 25730c7c) has a Ch07 Contract.lean byte-identical to the workspace Contract.lean and Submission.lean. Its project tree has no closure, slicing, filling or segment declaration and no match for the cbr_cc_/cbr_ccisp_/dmcbr_cc_/cmc_fcl_/rsd_cmr_/dtc_bc_tc_cl_cc names. All Mathlib lemmas used by the new proofs and the assembly are in the snapshot: liminf_le_of_frequently_le' (Order/LiminfLimsup.lean:365), Frequently.of_forall (Order/Filter/Basic.lean:779), measurableSet_lt (BorelSpace/Order.lean:245), tendsto_nhds_unique (Separation/Hausdorff.lean:180), IsCompact.union and Finset.isCompact_biUnion (Compactness/Compact.lean:520, 485), Bornology.IsBounded.thickening (MetricSpace/Thickening.lean:164), IsBounded.isCompact_closure (MetricSpace/Bounded.lean:328), extDeriv_constOfIsEmpty (DifferentialForm/Basic.lean:143), ContDiffBump.one_of_mem_closedBall and eventuallyEq_one_of_mem_ball (BumpFunction/Basic.lean:137, 169), segment_eq_image_lineMap (Convex/Segment.lean:216) and ENNReal.add_lt_top (ENNReal/Operations.lean:152). The SimonGMT facts are in Chapter06/Currents.lean (GeometricCurrentOn.ext, boundary_apply, boundary_boundary, WeaklyConvergesOn.boundary, tsupport_exteriorDerivative_subset, exteriorDerivativeTestOn), Chapter06/Mass.lean (massOn_mono, WeaklyConvergesOn.massOn_le_liminf) and Chapter06/CurrentLocalEquality.lean (support, isOpen_zeroRegion). The eight reused declarations are accepted DAG nodes with candidate commits and byte-identical frozen types. The accepted dmcbr_cc_slice_property_of_im needs BR(d) in every dimension, and the cbr/dmcbr filling nodes are unaccepted and need (ISO) for every m, so neither fits the node's fixed-P, in-range hypotheses. Hence the two fresh P-fixed children, whose Lean proofs (adapted from c74800df52 and fbb6f2da14) compile from exactly their declared siblings. The node type compiles from the children and its six dependencies with standard axioms only.
