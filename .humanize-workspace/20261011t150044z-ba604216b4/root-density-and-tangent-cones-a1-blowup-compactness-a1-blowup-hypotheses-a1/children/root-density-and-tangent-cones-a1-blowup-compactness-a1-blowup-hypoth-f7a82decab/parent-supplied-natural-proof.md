# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.blowup_hypotheses-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.blowup_hypotheses-a1.domain_boundary-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 0, 1, 2, 3 and 7 of the parent proof (Simon 7.3.1, chapter-07.txt lines 334–335: '∂η_{x,λ_j#}T = 0 in B_R(0) for sufficiently large j (because x ∉ spt ∂T)'). Dependencies: the siblings vanish_off_support = accepted Submission.dtc_vanish_off_support (V: for any current Y in any domain V and any test form ω in V, if tsupport ω is disjoint from spt Y then Y(ω) = 0) and blowup_algebra = accepted Submission.dtc_blowUp_algebra (ALG; used for λ > 0: (iii) spt(η_{x,λ#}Y) = η_{x,λ}(spt Y) for every k and Y ∈ 𝒟_k(U); (iv) ∂(η_{x,λ#}T) = η_{x,λ#}(∂T) for T ∈ 𝒟_{m+1}(U)). ALG (iii)–(iv) package exactly the unfolding of step 0 of the parent proof (S_j(ω) = T(η_j^#ω), ∂S_j(β) = ∂T(η_j^#β), tsupport η_j^#β ⊆ η_j⁻¹(tsupport β)).
Notation: λ_j := lams j > 0, η_j := dilation x λ_j, so η_j(y) = −λ_j⁻¹x + λ_j⁻¹y = λ_j⁻¹(y − x); S_j := blowUp T x λ_j ∈ 𝒟_{m+1}(η_j(U)); η_{j#}Y := blowUp Y x λ_j. For a current Y in a domain V, Z(Y) := zeroRegion Y (the union of the open W with compact closure W ⊆ V on which Y vanishes) is open (GeometricCurrentOn.isOpen_zeroRegion) and spt Y = V ∖ Z(Y). In degree m + 1, boundarySupport T = spt ∂T = T.boundary.support. 'For all large j' means eventually in atTop.
0. (The dilation.) For λ > 0, η := dilation x λ is the translation y ↦ y − x followed by the scaling v ↦ λ⁻¹v (λ⁻¹ ≠ 0); both are homeomorphisms of ℝ^P (Homeomorph.subRight, Homeomorph.smulOfNeZero), so η is a homeomorphism and in particular an open map. Moreover η(x + λz) = λ⁻¹(λz) = z for every z, and η(y) = z implies y = x + λ·λ⁻¹(y − x) = x + λz.
1. ((1)) η_j(U) is the image of the open set U under the homeomorphism η_j (step 0), hence open, for every j.
2. (A good radius.) Since x ∈ U and x ∉ spt ∂T = U ∖ Z(∂T), we have x ∈ Z(∂T). The set U ∩ Z(∂T) is open and contains x, so there is r > 0 with B_r(x) ⊆ U ∩ Z(∂T). (The parent chose closedBall(x, 2r) ⊆ U ∩ Z(∂T); the open ball B_r(x) plays the same role here.)
3. (Large j.) For every R ∈ ℝ, λ_jR → 0·R = 0, hence λ_jR < r for all large j (for R ≤ 0 this holds for every j).
4. ((2)) Let R ∈ ℝ, let j satisfy λ_jR < r (step 3) and let z ∈ closedBall(0, R), i.e. |z| ≤ R. Put y := x + λ_jz. Then |y − x| = λ_j|z| ≤ λ_jR < r, so y ∈ B_r(x) ⊆ U, and η_j(y) = z by step 0. Hence z ∈ η_j(U). Thus closedBall(0, R) ⊆ η_j(U) for all large j (for R < 0 the ball is empty).
5. ((3)) Let R ∈ ℝ, let j satisfy λ_jR < r (step 3), and let β ∈ 𝒟^m(η_j(U)) with tsupport β ⊆ B_R(0).
 (a) By ALG(iv) (λ_j > 0), ∂S_j = η_{j#}(∂T) as currents in 𝒟_m(η_j(U)); hence ∂S_j(β) = η_{j#}(∂T)(β).
 (b) By ALG(iii) applied to the m-current ∂T ∈ 𝒟_m(U), spt η_{j#}(∂T) = η_j(spt ∂T).
 (c) tsupport β ∩ η_j(spt ∂T) = ∅. Indeed, suppose z ∈ tsupport β and z = η_j(y) with y ∈ spt ∂T. By step 0, y = x + λ_jz. As z ∈ B_R(0), |z| < R, so |y − x| = λ_j|z| ≤ λ_jR < r and y ∈ B_r(x) ⊆ Z(∂T) by step 2. This contradicts y ∈ spt ∂T = U ∖ Z(∂T).
 (d) By (b) and (c), tsupport β is disjoint from spt η_{j#}(∂T). V, applied to the current η_{j#}(∂T) in the domain η_j(U) and the test form β, gives η_{j#}(∂T)(β) = 0; by (a), ∂S_j(β) = 0.
 (This is step 7 of the parent proof transported by η_j: there ∂S_j(β) = ∂T(η_j^#β), tsupport(η_j^#β) ⊆ η_j⁻¹(B_R(0)) = B_{λ_jR}(x) ⊆ Z(∂T), and V is applied to ∂T.)
6. (Conclusion.) Step 1 proves (1); steps 3–4 prove (2); steps 3 and 5 prove (3): for every R, for all j with λ_jR < r (all large j) and every β ∈ 𝒟^m(η_j(U)) with tsupport β ⊆ B_R(0), ∂S_j(β) = 0. ∎

Implementation hints: (1) rewrite dilation x λ as the coercion of (Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero λ⁻¹ _) and use isOpenMap; the radius comes from Metric.isOpen_iff applied to hU.inter T.boundary.isOpen_zeroRegion; (3) is rw [(Submission.dtc_blowUp_algebra P U x λ hλ).2.2.2 m T], apply Submission.dtc_vanish_off_support, rw [(…).2.2.1 m T.boundary, Set.disjoint_left].

Lean reference implementation (kernel-checked during this decomposition, Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b366308; place it in GMT/Ch07/Submission.lean inside `namespace GMT.Ch07` after the contract, with the contract's opens, after the dependency declarations; `#print axioms` gives propext, Classical.choice, Quot.sound). It compiled both in a scratch module consisting of the accepted commits a94d596 (which contains f64597f, Submission.dtc_blowUp_algebra) and 44ef61f (Submission.dtc_vanish_off_support), contract imports only, and in a scratch build of the grandparent's speculative Submission.

theorem Submission.dtc_bc_bh_blowUp_domain_boundary : ∀ (P m : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (m + 1)) (x : Euclid P), IsOpen U → x ∈ U → x ∉ boundarySupport T → ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) → (∀ j, IsOpen (dilation x (lams j) '' U)) ∧ (∀ R : ℝ, ∀ᶠ j in atTop, closedBall (0 : Euclid P) R ⊆ dilation x (lams j) '' U) ∧ (∀ R : ℝ, ∀ᶠ j in atTop, ∀ ω : TestFormOn (dilation x (lams j) '' U) m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ ball 0 R → (blowUp T x (lams j) (hlams j).ne').boundary ω = 0) := by
  intro P m U T x hU hxU hxb lams hlams hlim
  -- `η_{x,λ}(y) = λ⁻¹ • (y - x)`
  have hdil : ∀ (lam : ℝ) (y : Euclid P), dilation x lam y = lam⁻¹ • (y - x) := by
    intro lam y
    simp only [dilation, dilationCLM, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.coe_id', id_eq, smul_sub]
    abel
  -- `η_{x,λ}(x + λ z) = z` and `η_{x,λ}(y) = z → y = x + λ z`
  have hdil_inv : ∀ (lam : ℝ) (z : Euclid P), lam ≠ 0 → dilation x lam (x + lam • z) = z := by
    intro lam z hlam
    rw [hdil, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  have hdil_eq : ∀ (lam : ℝ) (y z : Euclid P), lam ≠ 0 → dilation x lam y = z → y = x + lam • z := by
    intro lam y z hlam h
    rw [← h, hdil, smul_smul, mul_inv_cancel₀ hlam, one_smul, add_sub_cancel]
  -- `λⱼ R` is eventually below any positive bound
  have hsmall : ∀ (R t : ℝ), 0 < t → ∀ᶠ j in atTop, lams j * R < t := by
    intro R t ht
    have h0 : Tendsto (fun j => lams j * R) atTop (𝓝 0) := by
      simpa using hlim.mul_const R
    exact (tendsto_order.1 h0).2 t ht
  -- (1) the blown-up domains are open
  have hopen : ∀ j, IsOpen (dilation x (lams j) '' U) := by
    intro j
    have hlam : lams j ≠ 0 := (hlams j).ne'
    have hfun : dilation x (lams j) =
        ((Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero (lams j)⁻¹ (inv_ne_zero hlam)) :
          Euclid P → Euclid P) := by
      funext y
      rw [hdil]
      rfl
    rw [hfun]
    exact ((Homeomorph.subRight x).trans
      (Homeomorph.smulOfNeZero (lams j)⁻¹ (inv_ne_zero hlam))).isOpenMap U hU
  -- a ball `B_r(x)` inside `U` and inside the zero region of `∂T`
  have hxZ : x ∈ T.boundary.zeroRegion := by
    by_contra h
    exact hxb ⟨hxU, h⟩
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 (hU.inter T.boundary.isOpen_zeroRegion) x ⟨hxU, hxZ⟩
  refine ⟨hopen, ?_, ?_⟩
  · -- (2) `closedBall 0 R ⊆ η_j(U)` once `λⱼ R < r`
    intro R
    filter_upwards [hsmall R r hr] with j hj
    intro z hz
    have hlam := hlams j
    refine ⟨x + lams j • z, (hrU ?_).1, hdil_inv (lams j) z hlam.ne'⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlam.le]
    rw [mem_closedBall, dist_zero_right] at hz
    calc lams j * ‖z‖ ≤ lams j * R := mul_le_mul_of_nonneg_left hz hlam.le
      _ < r := hj
  · -- (6) `∂S_j(β) = 0` for `spt β ⊆ B_R(0)` once `λⱼ R < r`
    intro R
    filter_upwards [hsmall R r hr] with j hj ω hω
    have hlam := hlams j
    have hALG := Submission.dtc_blowUp_algebra P U x (lams j) hlam
    rw [hALG.2.2.2 m T]
    apply Submission.dtc_vanish_off_support
    rw [hALG.2.2.1 m T.boundary, Set.disjoint_left]
    rintro z hz ⟨y, hy, hyz⟩
    have hyx : y = x + lams j • z := hdil_eq (lams j) y z hlam.ne' hyz
    have hzR := hω hz
    rw [mem_ball, dist_zero_right] at hzR
    have hyball : y ∈ ball x r := by
      rw [hyx, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlam.le]
      calc lams j * ‖z‖ ≤ lams j * R := mul_le_mul_of_nonneg_left hzR.le hlam.le
        _ < r := hj
    exact hy.2 (hrU hyball).2

## Key steps

1. η_j is a homeomorphism with η_j(x + λ_jz) = z, so η_j(U) is open and η_j(y) = z forces y = x + λ_jz.
2. x ∈ U ∩ zeroRegion(∂T) gives r > 0 with B_r(x) ⊆ U ∩ zeroRegion(∂T); λ_jR < r for all large j.
3. closedBall(0, R) ⊆ η_j(B_r(x)) ⊆ η_j(U) once λ_jR < r.
4. ∂S_j = η_{j#}∂T and spt η_{j#}∂T = η_j(spt ∂T) (ALG); tsupport β ⊆ B_R(0) misses η_j(spt ∂T) once λ_jR < r, so ∂S_j(β) = 0 by V.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c); cmp project/GMT/Ch07/Contract.lean and project/GMT/Ch07/Submission.lean against workspace GMT/Ch07/{Contract,Submission}.lean (identical)`
- `rg -n '^def dilation|^def dilationCLM|^def blowUp|^def HasMassDensity|^def unitBallVolume|^def boundarySupport|^def IsMinimizingIn|^def IsEmbeddedSubmanifold' project/GMT/Ch07/Contract.lean`
- `rg -n 'theorem measure_ball_lt_top|theorem measure_ball_pos|lemma nhdsGT_basis|theorem tendsto_nhdsWithin_iff|protected theorem div_lt_iff|theorem ofReal_mul|theorem ofReal_lt_ofReal_iff|def smulOfNeZero|theorem ContDiffOn.comp|theorem ContDiff.comp_contDiffOn|theorem ball_eq_empty|theorem isOpen_iff' mathlib/Mathlib`
- `rg -n 'Homeomorph.smulOfNeZero|def subRight' mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean mathlib/Mathlib/Topology`
- `rg -c 'dtc_bc_bh_|blowUp_massOn_ball_bounded|rescaled_retraction|blowUp_domain_boundary' project mathlib (no match)`
- `grep -n 'def GeometricCurrentOn.massOn|massAdmissibleOn|massOn_mono|le_massOn' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean; grep -n 'zeroRegion|def GeometricCurrentOn.support|isOpen_zeroRegion|VanishesOn' simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean; grep -n 'TestFormOn|GeometricCurrentOn.boundary|boundary_apply' simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `python3 -I: dag.json lean_name inventory (dtc_blowUp_scaling, dtc_vanish_off_support, dtc_blowUp_algebra accepted with byte-identical lean_statement; dtc_bc_bh_* absent); isolated-comparator-result.json of the three reused nodes (passed); node.json of the selected node (dependency_workspaces = local_retraction only); git log of implementation bases of blowup_compactness, cone_lemma, radial_tangency`
- `python3 -I: verifier/gmt-compare.py contract_scope + child challenge/solution modules; verifier/lean_contract.py validate_lean_statement on all six child types`
- `lean (LEAN_PATH of lake-packages-25730c7c): Challenge_<key>.lean for the six children, the selected type and local_retraction; Assembly.lean (conditional, comparator scope); C1/C2/C3 proofs and concrete assembly against scratch bases from commits a94d596 + 44ef61f and against frozen b4d606d; FromJson.lean recompiled from the final JSON; #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LeftRightNhds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/NhdsWithin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-blowup-hypotheses-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1-blowup-structure-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1/parent-implementation-base.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/bh_work/check/Assembly.lean`
- `/tmp/bh_work/lib2/RealBase.lean`
- `/tmp/bh_work/lib2/FromJson.lean`
- `/tmp/bh_work/lib2/C3Frozen.lean`

The snapshot contract (project b4d606d, Mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean. Every Mathlib lemma named in the child proofs exists at the pin; ENNReal.div_lt_iff and ofReal_mul are under Mathlib/Basic/ENNReal. The SimonGMT objects used (massOn, massAdmissibleOn, zeroRegion, isOpen_zeroRegion, support, boundary) are in the pinned package. The snapshot has no blow-up lemmas; those are the accepted run declarations dtc_blowUp_scaling, dtc_vanish_off_support and dtc_blowUp_algebra. Their frozen types are byte-identical to the reuse children, and they passed the isolated comparator. No dtc_bc_bh_* name occurs anywhere (no match). All six child types elaborate in the comparator scope. Kernel-checked proofs of the three new children and the assembly use only propext, Classical.choice and Quot.sound.
