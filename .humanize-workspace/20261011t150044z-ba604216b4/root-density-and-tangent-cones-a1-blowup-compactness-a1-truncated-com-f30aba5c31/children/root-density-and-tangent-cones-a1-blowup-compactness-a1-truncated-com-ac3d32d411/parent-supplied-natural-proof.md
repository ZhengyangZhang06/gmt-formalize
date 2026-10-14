# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.closure_compact-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.closure_compact-a1.isp_of_im-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the supplied proof (parent V4(i)): "If X and ∂X are IM with finite masses then X has ISP: for admissible representations and f, (SL) gives slices Z_t with locally finite mass for a.e. t ((MM)); A_t = X⌞{f<t} is IM by (IMC)(b) and (RU), likewise B_t; ∂A_t = B_t + Z_t has locally finite mass, so it is IM by BR_P(d) in ℝ^P, and Z_t = ∂A_t − B_t is IM by (IMC)(c)." The finite-mass hypotheses of step 5 are not needed. This is the argument of the accepted dmcbr_cc_slice_property_of_im, which applies BR only with U := ℝ^P in the given dimension P; so BR_P(d) at the single dimension P suffices. Siblings used: restrict_im (cbr_ccisp_restrict_isIntegerMultiplicity), ae_mass_finite (cbr_ccisp_ae_massOn_lt_top), mass_le_measure (cmc_fcl_massOn_le_measure_inter) and current_algebra (cbr_cc_current_algebra), part (b). Notation: M_W(Z) := Z.massOn W; E_t := {x : f(x) < t}; ℝ^P is the open set U := univ; |α| := covectorEuclideanNorm α.
1. Setup. Let X ∈ 𝒟_{d+1}(ℝ^P) be IM with ∂X IM. Let (μ, ξ) and (μ', ξ') be admissible representations of X and ∂X: μ(K), μ'(K) < ∞ for every compact K; ξ, ξ' are a.e. strongly measurable; |ξ(x)(α)| ≤ |α| for μ-a.e. x and |ξ'(x)(α)| ≤ |α| for μ'-a.e. x (all covectors α); X(ω) = ∫ξ(ω)dμ and ∂X(η) = ∫ξ'(η)dμ' for all test forms. Let f be L-Lipschitz. Write (IMC) = (a) ∧ (b) ∧ (c) ∧ (d). Since f is continuous, every E_t is Borel (measurableSet_lt).
2. Slices. Apply (SL) with U := ℝ^P, k := d, T := X, the pairs (μ, ξ), (μ', ξ'), f and L. Its hypotheses are exactly the admissibility conditions of step 1 (a compact K ⊆ ℝ^P has μ(K), μ'(K) < ∞). It gives currents A_t ∈ 𝒟_{d+1}(ℝ^P) and B_t ∈ 𝒟_d(ℝ^P) (t ∈ ℝ) with A_t(ω) = ∫_{E_t}ξ(ω)dμ and B_t(η) = ∫_{E_t}ξ'(η)dμ' for all test forms. Moreover, with Z_t := ∂A_t − B_t, M_W(Z_t) ≤ L·liminf_{h↓0} h⁻¹μ(W ∩ {t − h < f < t}) for every open W and every t.
3. Null set. Apply ae_mass_finite with (MM), P, q := d, U := ℝ^P, Z := (t ↦ Z_t), μ (finite on compact sets), the continuous f, L and the bound of step 2. It gives a Lebesgue-null set N ⊂ ℝ such that for every t ∉ N, M_W(Z_t) < ∞ for every bounded W ⊆ ℝ^P.
4. Reduction. Fix t ∉ N and currents A ∈ 𝒟_{d+1}(ℝ^P), B ∈ 𝒟_d(ℝ^P) with A(ω) = ∫_{E_t}ξ(ω)dμ and B(η) = ∫_{E_t}ξ'(η)dμ' for all test forms. Then A agrees with A_t and B with B_t on every test form, so A = A_t and B = B_t (GeometricCurrentOn.ext). It remains to show that Z_t = ∂A_t − B_t is IM.
5. A_t is IM. Apply restrict_im with (IMC)(b), (IMC)(d), (RU), P, q := d + 1, U := ℝ^P, the IM current X, A := A_t, (μ, ξ) and E := E_t. Its hypotheses hold: μ is finite on compact sets; ξ is μ-a.e. strongly measurable with the a.e. unit bound; X(ω) = ∫ξ(ω)dμ; E_t is Borel; and A_t(ω) = ∫_{E_t}ξ(ω)dμ.
6. B_t is IM. Apply restrict_im in the same way with q := d, the IM current ∂X, A := B_t, (μ', ξ') and E := E_t.
7. ∂A_t is IM. We apply BR_P(d) with U := ℝ^P and R := A_t, which is IM by step 5. Let W be open with W ⊂⊂ ℝ^P, i.e. closure W is compact.
 (i) W ⊆ closure W is bounded, so M_W(Z_t) < ∞ by step 3.
 (ii) Apply mass_le_measure with X := B_t, (μ', ξ'), E := E_t and V := W, using the a.e. unit bound of ξ' and the formula for B_t. It gives M_W(B_t) ≤ μ'(E_t ∩ W) ≤ μ'(closure W) < ∞, since closure W is compact.
 (iii) For every test d-form η, ∂A_t(η) = 1·Z_t(η) + 1·B_t(η), because Z_t(η) = ∂A_t(η) − B_t(η). So current_algebra (b) with p = q = 1 gives M_W(∂A_t) ≤ M_W(Z_t) + M_W(B_t) < ∞.
 Hence BR_P(d) shows that ∂A_t is IM.
8. Conclusion. ℝ^P is open and ∂A_t, B_t are IM by steps 7 and 6, so Z_t = ∂A_t − B_t is IM by (IMC)(c). By step 4, ∂A − B = Z_t is IM for every t ∉ N and every pair A, B with the slice formulas, i.e. for L¹-a.e. t. Since (μ, ξ), (μ', ξ') and f were arbitrary, X has the integer slice property. ∎
Appendix (verified Lean). This tactic proof of exactly the frozen statement compiled with lake env lean after import GMT.Ch07.Submission inside namespace GMT.Ch07 with the contract's opens, with the sibling declarations Submission.cbr_cc_current_algebra, Submission.cbr_ccisp_restrict_isIntegerMultiplicity, Submission.cbr_ccisp_ae_massOn_lt_top, Submission.cmc_fcl_massOn_le_measure_inter available at their frozen types; #print axioms: propext, Classical.choice, Quot.sound and those sibling declarations.
  intro hIMC hSL hMM hRU P d hBR X hX hXb μ μ' ξ ξ' hμ hμ' hξm hξ'm hξb hξ'b hXrep hXbrep f L hf
  obtain ⟨-, hIMCb, hIMCc, hIMCd⟩ := hIMC
  -- Step 2: slices `A_t`, `B_t` from (SL) in `U = ℝᴾ`
  obtain ⟨At, Bt, hAt, hBt, -, hmass, -⟩ := hSL P d univ X μ μ' ξ ξ' f L isOpen_univ
    (fun K hK _ => hμ K hK) (fun K hK _ => hμ' K hK) hξm hξ'm hξb hξ'b hXrep hXbrep hf
  -- Step 3: for a.e. `t`, `Z_t = ∂A_t − B_t` has finite mass on bounded sets
  have hfin := Submission.cbr_ccisp_ae_massOn_lt_top hMM P d univ
    (fun t => (At t).boundary - Bt t) μ f L hf.continuous hμ hmass
  filter_upwards [hfin] with t ht A B hA hB
  -- Step 4: `A = A_t` and `B = B_t`
  rw [GeometricCurrentOn.ext fun ω => (hA ω).trans (hAt t ω).symm,
    GeometricCurrentOn.ext fun η => (hB η).trans (hBt t η).symm]
  have hE : MeasurableSet {x | f x < t} :=
    measurableSet_lt hf.continuous.measurable measurable_const
  -- Steps 5–6: `A_t` and `B_t` are integer multiplicity
  have hAIM : IsIntegerMultiplicity (At t) :=
    Submission.cbr_ccisp_restrict_isIntegerMultiplicity hIMCb hIMCd hRU P (d + 1) univ X (At t)
      μ ξ {x | f x < t} isOpen_univ hX (fun K hK _ => hμ K hK) hξm hξb hXrep hE (hAt t)
  have hBIM : IsIntegerMultiplicity (Bt t) :=
    Submission.cbr_ccisp_restrict_isIntegerMultiplicity hIMCb hIMCd hRU P d univ X.boundary
      (Bt t) μ' ξ' {x | f x < t} isOpen_univ hXb (fun K hK _ => hμ' K hK) hξ'm hξ'b hXbrep hE
      (hBt t)
  -- Step 7: `M_W(∂A_t) ≤ M_W(Z_t) + M_W(B_t) < ∞` for `W ⊂⊂ ℝᴾ`, so `BR_P(d)` applies
  have hdAIM : IsIntegerMultiplicity (At t).boundary := by
    refine hBR univ (At t) isOpen_univ hAIM fun W _ hWU => ?_
    have hZ : ((At t).boundary - Bt t).massOn W < ∞ :=
      ht W (hWU.1.isBounded.subset subset_closure)
    have hBW : (Bt t).massOn W < ∞ :=
      (Submission.cmc_fcl_massOn_le_measure_inter P d univ (Bt t) μ' ξ' {x | f x < t} W hξ'b
        (hBt t)).trans_lt
        ((measure_mono (inter_subset_right.trans subset_closure)).trans_lt (hμ' _ hWU.1))
    have hsplit := Submission.cbr_cc_current_algebra.2.1 P d univ (At t).boundary
      ((At t).boundary - Bt t) (Bt t) 1 1
      (fun η => by
        rw [Int.cast_one, one_mul, one_mul]
        exact (sub_add_cancel ((At t).boundary η) (Bt t η)).symm) W
    simp only [Int.natAbs_one, Nat.cast_one, one_mul] at hsplit
    exact hsplit.trans_lt (ENNReal.add_lt_top.2 ⟨hZ, hBW⟩)
  -- Step 8: `Z_t = ∂A_t − B_t` is integer multiplicity by (IMC)(c)
  exact hIMCc P d univ (At t).boundary (Bt t) isOpen_univ hdAIM hBIM

## Key steps

1. (SL) in ℝ^P gives A_t, B_t and the liminf mass bound for Z_t = ∂A_t − B_t; ae_mass_finite with (MM) makes M_W(Z_t) finite on bounded W for a.e. t.
2. Currents with the slice formulas equal A_t and B_t; restrict_im ((IMC)(b), (IMC)(d), (RU)) makes A_t and B_t IM.
3. For W ⊂⊂ ℝ^P, M_W(∂A_t) ≤ M_W(Z_t) + μ'(closure W) < ∞ (mass_le_measure, current_algebra (b)), so BR_P(d) with U := ℝ^P makes ∂A_t IM.
4. (IMC)(c) makes Z_t = ∂A_t − B_t IM for a.e. t, which is the integer slice property.

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
