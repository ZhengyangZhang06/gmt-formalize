# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.blowup_hypotheses-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.blowup_hypotheses-a1.rescaled_retraction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 8 of the parent proof (the retractions onto N used in Simon's proof of the compactness theorem 7.2.4 and Remark 7.2.5(2), rescaled for the blow-ups of 7.3.1, chapter-07.txt lines 333–337). No dependencies: the retraction π and its properties (i)–(iv) are hypotheses here. They are exactly the conclusion of local_retraction, which the selected parent applies to N and x before invoking this lemma.
Notation: λ_j := lams j > 0, η_j := dilation x λ_j, so η_j(y) = −λ_j⁻¹x + λ_j⁻¹y = λ_j⁻¹(y − x). For every z, η_j(x + λ_jz) = z, and η_j(y') = z implies y' = x + λ_jz. Define, for every j ∈ ℕ,
 π_j(z) := η_j(π(x + λ_jz)) = λ_j⁻¹(π(x + λ_jz) − x)
(in Lean: πs := fun j z => dilation x (lams j) (π (x + lams j • z))). 'For all large j' means eventually in atTop.
1. (Radii.) Since U is open and x ∈ U, there is r₀ > 0 with B_{r₀}(x) ⊆ U. By (iv) with η = 1 there is s₁ with 0 < s₁ ≤ δ and |π(y) − π(z)| ≤ 2|y − z| for all y, z ∈ B_{s₁}(x). Since x ∈ N ∩ B_δ(x) (δ > 0), (iii) gives π(x) = x.
2. (Scaled points.) If λ > 0, t ∈ ℝ, λG ≤ t and |z| < G, then x + λz ∈ B_t(x), because |(x + λz) − x| = λ|z| < λG ≤ t.
3. (Large j.) For every t > 0, λ_jG → 0·G = 0, so λ_jG < t for all large j.
4. (The four properties.) Let j satisfy λ_jG < min(s₁, r₀/2) (all large j by step 3). Then λ_jG ≤ s₁ ≤ δ and λ_jG ≤ r₀/2. By step 2, the affine map a_j(z) := x + λ_jz maps B_G(0) into B_{s₁}(x) ⊆ B_δ(x).
 (a) (Key estimate.) Let z ∈ B_G(0) and y := x + λ_jz ∈ B_{s₁}(x). By step 1, |π(y) − x| = |π(y) − π(x)| ≤ 2|y − x| = 2λ_j|z|. Hence |π(y) − x| < 2λ_jG ≤ r₀, so π(y) ∈ B_{r₀}(x) ⊆ U; and π(y) ∈ N by (ii), since y ∈ B_δ(x). Thus π(y) ∈ U ∩ N.
 (b) (C¹.) a_j is affine, hence C^∞, and maps B_G(0) into B_δ(x), where π is C¹ by (i); so π∘a_j is C¹ on B_G(0) (ContDiffOn.comp). η_j is a constant plus the continuous linear map λ_j⁻¹·id, hence C^∞, so π_j = η_j∘(π∘a_j) is C¹ on B_G(0) (ContDiff.comp_contDiffOn).
 (c) (Maps into η_j(U ∩ N).) For z ∈ B_G(0), π_j(z) = η_j(π(x + λ_jz)) with π(x + λ_jz) ∈ U ∩ N by (a); so π_j(z) ∈ η_j(U ∩ N).
 (d) (Identity.) Let z ∈ η_j(U ∩ N) ∩ B_G(0), say z = η_j(y') with y' ∈ U ∩ N. Then x + λ_jz = x + λ_jλ_j⁻¹(y' − x) = y', and y' = a_j(z) ∈ B_δ(x) because z ∈ B_G(0). As y' ∈ N ∩ B_δ(x), (iii) gives π(y') = y'. Hence π_j(z) = η_j(π(y')) = η_j(y') = z.
 (e) (Growth.) For z ∈ B_G(0), |π_j(z)| = |λ_j⁻¹(π(x + λ_jz) − x)| = λ_j⁻¹|π(x + λ_jz) − x| ≤ λ_j⁻¹·2λ_j|z| = 2|z| by (a).
 Thus, for all large j, π_j is C¹ on B_G(0), maps B_G(0) into η_j(U ∩ N), is the identity on η_j(U ∩ N) ∩ B_G(0), and satisfies |π_j(z)| ≤ 2|z| on B_G(0).
5. (Almost isometry.) Let η > 0. By (iv) there is s with 0 < s ≤ δ and |π(y) − π(z)| ≤ (1 + η)|y − z| for y, z ∈ B_s(x). By step 3, λ_jG < s for all large j; fix such j and y, z ∈ B_G(0). By step 2, x + λ_jy and x + λ_jz lie in B_s(x). Since
 π_j(y) − π_j(z) = λ_j⁻¹(π(x + λ_jy) − x) − λ_j⁻¹(π(x + λ_jz) − x) = λ_j⁻¹(π(x + λ_jy) − π(x + λ_jz))
 and |(x + λ_jy) − (x + λ_jz)| = λ_j|y − z|, we get |π_j(y) − π_j(z)| ≤ λ_j⁻¹(1 + η)λ_j|y − z| = (1 + η)|y − z|.
6. (Conclusion.) The family (π_j)_j does not depend on η; step 4 proves the first (eventual) conjunct and step 5 the second, for every G > 0. ∎

Lean reference implementation (kernel-checked during this decomposition, Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b366308; place it in GMT/Ch07/Submission.lean inside `namespace GMT.Ch07` after the contract, with the contract's opens, after the dependency declarations; `#print axioms` gives propext, Classical.choice, Quot.sound). It compiled against the frozen contract (import GMT.Ch07.Submission at commit b4d606d; it uses no Submission lemma) and in the scratch builds used for the siblings.

theorem Submission.dtc_bc_bh_rescaled_retraction : ∀ (P : ℕ) (U N : Set (Euclid P)) (x : Euclid P) (δ : ℝ) (π : Euclid P → Euclid P), IsOpen U → x ∈ U → x ∈ N → 0 < δ → ContDiffOn ℝ 1 π (ball x δ) → MapsTo π (ball x δ) N → (∀ y ∈ N ∩ ball x δ, π y = y) → (∀ η : ℝ, 0 < η → ∃ s : ℝ, 0 < s ∧ s ≤ δ ∧ ∀ y ∈ ball x s, ∀ z ∈ ball x s, ‖π y - π z‖ ≤ (1 + η) * ‖y - z‖) → ∀ lams : ℕ → ℝ, (∀ j, 0 < lams j) → Tendsto lams atTop (𝓝 0) → ∀ G : ℝ, 0 < G → ∃ πs : ℕ → Euclid P → Euclid P, (∀ᶠ j in atTop, ContDiffOn ℝ 1 (πs j) (ball 0 G) ∧ MapsTo (πs j) (ball 0 G) (dilation x (lams j) '' (U ∩ N)) ∧ (∀ y ∈ dilation x (lams j) '' (U ∩ N) ∩ ball 0 G, πs j y = y) ∧ ∀ y ∈ ball 0 G, ‖πs j y‖ ≤ 2 * ‖y‖) ∧ ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ y ∈ ball 0 G, ∀ z ∈ ball 0 G, ‖πs j y - πs j z‖ ≤ (1 + η) * ‖y - z‖ := by
  intro P U N x δ π hU hxU hxN hδ hC hmaps hid hlip lams hlams hlim G hG
  -- a ball `B_{r₀}(x) ⊆ U`
  obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.isOpen_iff.1 hU x hxU
  -- `π` is `2`-Lipschitz on `B_{s₁}(x)`
  obtain ⟨s₁, hs₁, hs₁δ, hlip1⟩ := hlip 1 one_pos
  have hπx : π x = x := hid x ⟨hxN, mem_ball_self hδ⟩
  -- `η_{x,λ}(y) = λ⁻¹ • (y - x)`
  have hdil : ∀ (lam : ℝ) (y : Euclid P), dilation x lam y = lam⁻¹ • (y - x) := by
    intro lam y
    simp only [dilation, dilationCLM, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.coe_id', id_eq, smul_sub]
    abel
  -- `x + λ • z ∈ B_t(x)` when `z ∈ B_G(0)` and `λ G ≤ t`
  have hmem : ∀ (lam t : ℝ) (z : Euclid P), 0 < lam → lam * G ≤ t → z ∈ ball (0 : Euclid P) G →
      x + lam • z ∈ ball x t := by
    intro lam t z hlam hlt hz
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlam.le]
    rw [mem_ball, dist_zero_right] at hz
    calc lam * ‖z‖ < lam * G := mul_lt_mul_of_pos_left hz hlam
      _ ≤ t := hlt
  have hsmall : ∀ t : ℝ, 0 < t → ∀ᶠ j in atTop, lams j * G < t := by
    intro t ht
    have h0 : Tendsto (fun j => lams j * G) atTop (𝓝 0) := by
      simpa using hlim.mul_const G
    exact (tendsto_order.1 h0).2 t ht
  refine ⟨fun j z => dilation x (lams j) (π (x + lams j • z)), ?_, ?_⟩
  · filter_upwards [hsmall (min s₁ (r₀ / 2)) (lt_min hs₁ (half_pos hr₀))] with j hj
    have hlam := hlams j
    have hj₁ : lams j * G ≤ s₁ := hj.le.trans (min_le_left _ _)
    have hj₂ : lams j * G ≤ r₀ / 2 := hj.le.trans (min_le_right _ _)
    have hjδ : lams j * G ≤ δ := hj₁.trans hs₁δ
    -- the affine map `z ↦ x + λⱼ z` maps `B_G(0)` into `B_δ(x)`
    have hmapsδ : MapsTo (fun z : Euclid P => x + lams j • z) (ball 0 G) (ball x δ) :=
      fun z hz => hmem (lams j) δ z hlam hjδ hz
    -- `π(x + λⱼ z) ∈ U ∩ N` and `|π(x + λⱼ z) - x| ≤ 2 λⱼ |z|`
    have hkey : ∀ z ∈ ball (0 : Euclid P) G, π (x + lams j • z) ∈ U ∩ N ∧
        ‖π (x + lams j • z) - x‖ ≤ 2 * (lams j * ‖z‖) := by
      intro z hz
      have hy : x + lams j • z ∈ ball x s₁ := hmem (lams j) s₁ z hlam hj₁ hz
      have hbd : ‖π (x + lams j • z) - x‖ ≤ 2 * (lams j * ‖z‖) := by
        have := hlip1 _ hy x (mem_ball_self hs₁)
        rw [hπx] at this
        calc ‖π (x + lams j • z) - x‖ ≤ (1 + 1) * ‖x + lams j • z - x‖ := this
          _ = 2 * (lams j * ‖z‖) := by
            rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlam.le]; norm_num
      refine ⟨⟨hr₀U ?_, hmaps (hmapsδ hz)⟩, hbd⟩
      rw [mem_ball, dist_eq_norm]
      rw [mem_ball, dist_zero_right] at hz
      calc ‖π (x + lams j • z) - x‖ ≤ 2 * (lams j * ‖z‖) := hbd
        _ < 2 * (lams j * G) := by
          have := mul_lt_mul_of_pos_left hz hlam
          linarith
        _ ≤ r₀ := by linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- `C¹` on `B_G(0)`
      have hdilC : ContDiff ℝ 1 (dilation x (lams j)) := by
        unfold dilation
        exact contDiff_const.add (dilationCLM P (lams j)).contDiff
      have haff : ContDiff ℝ 1 (fun z : Euclid P => x + lams j • z) :=
        contDiff_const.add (contDiff_id.const_smul (lams j))
      exact hdilC.comp_contDiffOn (hC.comp haff.contDiffOn hmapsδ)
    · -- maps `B_G(0)` into `η_j(U ∩ N)`
      intro z hz
      exact ⟨π (x + lams j • z), (hkey z hz).1, rfl⟩
    · -- identity on `η_j(U ∩ N) ∩ B_G(0)`
      rintro z ⟨⟨y', hy', rfl⟩, hz⟩
      have hinv : x + lams j • dilation x (lams j) y' = y' := by
        rw [hdil, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul, add_sub_cancel]
      show dilation x (lams j) (π (x + lams j • dilation x (lams j) y')) = dilation x (lams j) y'
      rw [hinv, hid y' ⟨hy'.2, ?_⟩]
      rw [← hinv]
      exact hmapsδ hz
    · -- `|π_j(z)| ≤ 2|z|`
      intro z hz
      show ‖dilation x (lams j) (π (x + lams j • z))‖ ≤ 2 * ‖z‖
      rw [hdil, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hlam.le)]
      calc (lams j)⁻¹ * ‖π (x + lams j • z) - x‖ ≤ (lams j)⁻¹ * (2 * (lams j * ‖z‖)) :=
            mul_le_mul_of_nonneg_left (hkey z hz).2 (inv_nonneg.2 hlam.le)
        _ = 2 * ‖z‖ := by field_simp
  · intro η hη
    obtain ⟨s, hs, hsδ, hlipη⟩ := hlip η hη
    filter_upwards [hsmall s hs] with j hj y hy z hz
    have hlam := hlams j
    have hy' := hmem (lams j) s y hlam hj.le hy
    have hz' := hmem (lams j) s z hlam hj.le hz
    show ‖dilation x (lams j) (π (x + lams j • y)) - dilation x (lams j) (π (x + lams j • z))‖ ≤
      (1 + η) * ‖y - z‖
    rw [hdil, hdil, ← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hlam.le)]
    have h1 := hlipη _ hy' _ hz'
    have h2 : ‖x + lams j • y - (x + lams j • z)‖ = lams j * ‖y - z‖ := by
      rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg hlam.le]
    have h3 : π (x + lams j • y) - x - (π (x + lams j • z) - x) =
        π (x + lams j • y) - π (x + lams j • z) := by abel
    rw [h3]
    calc (lams j)⁻¹ * ‖π (x + lams j • y) - π (x + lams j • z)‖
        ≤ (lams j)⁻¹ * ((1 + η) * (lams j * ‖y - z‖)) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hlam.le)
      _ = (1 + η) * ‖y - z‖ := by field_simp

## Key steps

1. Choose r₀ > 0 with B_{r₀}(x) ⊆ U and s₁ ∈ (0, δ] with π 2-Lipschitz on B_{s₁}(x); π(x) = x by (iii).
2. Define π_j(z) := η_j(π(x + λ_jz)); once λ_jG < min(s₁, r₀/2), x + λ_jz ∈ B_{s₁}(x) ⊆ B_δ(x) for z ∈ B_G(0).
3. Then π(x + λ_jz) ∈ U ∩ N with |π(x + λ_jz) − x| ≤ 2λ_j|z|, which gives C¹ (chain rule), MapsTo into η_j(U ∩ N), the identity on η_j(U ∩ N) ∩ B_G(0) via (iii), and |π_j(z)| ≤ 2|z|.
4. For η > 0 and λ_jG < s(η), the (1+η)-Lipschitz bound of π on B_{s(η)}(x) rescales to |π_j(y) − π_j(z)| ≤ (1+η)|y − z|.

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
