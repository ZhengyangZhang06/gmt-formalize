# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.blowup_hypotheses-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.blowup_hypotheses-a1.mass_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent proof (Simon 7.3.1, proof display (1), chapter-07.txt lines 329–335: (ω_nRⁿ)⁻¹M_{B_R(0)}(η_{x,λ_j#}T) = (ω_nλ_jⁿRⁿ)⁻¹M_{B_{λ_jR}(x)}(T) → Θⁿ(μ_T, x) 'for each R > 0, and hence sup_j M_{B_R(0)}(η_{x,λ_j#}T) < ∞'). Dependency: the sibling blowup_scaling, i.e. the accepted declaration Submission.dtc_blowUp_scaling (BU). Only its part (1) is used: for U open, n > 0 and λ > 0, M_{η_{x,λ}(W)}(η_{x,λ#}T) = ofReal(λ⁻¹ⁿ)·M_W(T) for every W ⊆ ℝ^P.
Notation: λ_j := lams j > 0, η_j := dilation x λ_j, so η_j(y) = −λ_j⁻¹x + λ_j⁻¹y = λ_j⁻¹(y − x); S_j := blowUp T x λ_j ∈ 𝒟_n(η_j(U)). For a current Y in a domain V and W ⊆ ℝ^P, M_W(Y) = Y.massOn W is the supremum in [0, ∞] of ofReal(Y(ω)) over the admissible forms ω ∈ 𝒟ⁿ(V) with tsupport ω ⊆ W and Euclidean coefficient norm at most 1 at every point (SimonGMT massOn, massAdmissibleOn). ω_n := unitBallVolume n = volume(ball(0, 1)) in ℝⁿ. 'For all large j' means 'for all j ≥ some j₀', i.e. eventually in atTop.
1. (Case R ≤ 0.) Then B_R(0) = ball 0 R = ∅. Let ω be admissible for M_∅(S_j). If ω(y) ≠ 0 for some y, then y ∈ support ω ⊆ tsupport ω ⊆ ∅, which is impossible; so ω = 0 and S_j(ω) = S_j(0) = 0 by linearity. Hence every element of the set whose supremum defines M_∅(S_j) equals ofReal 0 = 0, so M_{B_R(0)}(S_j) = 0 for every j. Take c := 0 (c ≠ ∞). This proves the claim for R ≤ 0; from now on R > 0.
2. (The constant ω_n.) 0 < ω_n < ∞: the unit ball of ℝⁿ is a nonempty open set and Lebesgue measure charges nonempty open sets (Metric.measure_ball_pos), and balls in the proper space ℝⁿ have finite Lebesgue measure (measure_ball_lt_top). Write F(ρ) := T.massOn(B_ρ(x)) / (ω_n·ofReal(ρⁿ)).
3. (A density bound near 0.) HasMassDensity T x θ says θ ≥ 0 and F(ρ) → ofReal θ in [0, ∞] as ρ → 0⁺ (along 𝓝[>] 0). Since θ < θ + 1 and θ + 1 > 0, ofReal θ < ofReal(θ + 1) (ENNReal.ofReal_lt_ofReal_iff). By the order-topology characterization of the limit, F(ρ) < ofReal(θ + 1) eventually along 𝓝[>] 0; as the intervals (0, u), u > 0, form a basis of 𝓝[>] 0 (nhdsGT_basis), there is s₀ > 0 with F(ρ) < ofReal(θ + 1) for every ρ ∈ (0, s₀).
4. (Mass bound for T.) Let ρ ∈ (0, s₀) and b(ρ) := ω_n·ofReal(ρⁿ). Then b(ρ) ≠ 0 (ω_n ≠ 0 and ρⁿ > 0) and b(ρ) ≠ ∞ (ω_n ≠ ∞). For such b, a / b < c ⟺ a < c·b in [0, ∞] (ENNReal.div_lt_iff), so step 3 gives T.massOn(B_ρ(x)) < ofReal(θ + 1)·(ω_n·ofReal(ρⁿ)); in particular T.massOn(B_ρ(x)) ≤ ofReal(θ + 1)·(ω_n·ofReal(ρⁿ)).
5. (The constant c.) Put c := ofReal(θ + 1)·(ω_n·ofReal(Rⁿ)). It is finite, being a product of finite factors (ω_n ≠ ∞ by step 2).
6. (Large j.) Since λ_j → 0, also λ_jR → 0·R = 0, so λ_jR < s₀ for all large j. Fix such a j and write λ := λ_j > 0; then 0 < λR < s₀ (R > 0).
7. (Image of the ball.) η_j(B_{λR}(x)) = B_R(0). If |y − x| < λR then |η_j(y)| = |λ⁻¹(y − x)| = λ⁻¹|y − x| < λ⁻¹λR = R. Conversely, if |z| < R then y := x + λz satisfies |y − x| = λ|z| < λR and η_j(y) = λ⁻¹(x + λz − x) = z.
8. (Scaling.) By step 7 and BU(1) with W := B_{λR}(x) (U open, n > 0, λ > 0):
 S_j.massOn(B_R(0)) = S_j.massOn(η_j(B_{λR}(x))) = ofReal(λ⁻¹ⁿ)·T.massOn(B_{λR}(x)).
 By step 4 with ρ := λR ∈ (0, s₀) and monotonicity of multiplication in [0, ∞],
 S_j.massOn(B_R(0)) ≤ ofReal(λ⁻¹ⁿ)·(ofReal(θ + 1)·(ω_n·ofReal((λR)ⁿ))) = ofReal(θ + 1)·(ω_n·(ofReal(λ⁻¹ⁿ)·ofReal((λR)ⁿ))) = ofReal(θ + 1)·(ω_n·ofReal(λ⁻¹ⁿ·(λR)ⁿ)) = ofReal(θ + 1)·(ω_n·ofReal(Rⁿ)) = c,
 using commutativity and associativity in [0, ∞], ofReal(a)·ofReal(b) = ofReal(ab) for a = λ⁻¹ⁿ ≥ 0 (ENNReal.ofReal_mul), and λ⁻¹ⁿ(λR)ⁿ = (λ⁻¹λ)ⁿRⁿ = Rⁿ.
9. (Conclusion.) Steps 5–8 give c ≠ ∞ with S_j.massOn(B_R(0)) ≤ c for all large j when R > 0, and step 1 handles R ≤ 0. Hence for every R ∈ ℝ there is c ∈ [0, ∞) with M_{B_R(0)}(S_j) ≤ c for all large j. ∎

Implementation hints: the eventual statement in step 6 is (tendsto_order.1 (by simpa using hlim.mul_const R)).2 s₀ hs₀; step 3 is (nhdsGT_basis 0).eventually_iff.1 ((tendsto_order.1 hlim_θ).2 _ hlt); step 1 uses ball_eq_empty, sSup_le, Subtype.ext and subset_tsupport.

Lean reference implementation (kernel-checked during this decomposition, Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b366308; place it in GMT/Ch07/Submission.lean inside `namespace GMT.Ch07` after the contract, with the contract's opens, after the dependency declarations; `#print axioms` gives propext, Classical.choice, Quot.sound). It compiled both in a scratch module consisting of the accepted commit a94d596 of Submission.dtc_blowUp_scaling (contract imports only) and in a scratch build of the grandparent's speculative Submission.

theorem Submission.dtc_bc_bh_blowUp_massOn_ball_bounded : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (θ : ℝ), IsOpen U → 0 < n → HasMassDensity T x θ → ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) → ∀ R : ℝ, ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ᶠ j in atTop, (blowUp T x (lams j) (hlams j).ne').massOn (ball 0 R) ≤ c := by
  intro P n U T x θ hU hn hθ lams hlams hlim R
  obtain ⟨hθ0, hlimθ⟩ := hθ
  by_cases hR : 0 < R
  swap
  · -- `R ≤ 0`: `B_R(0) = ∅`, the only admissible form is `0`, so the mass is `0`
    refine ⟨0, ENNReal.zero_ne_top, Eventually.of_forall fun j => ?_⟩
    have hempty : ball (0 : Euclid P) R = ∅ := ball_eq_empty.2 (not_lt.1 hR)
    rw [hempty]
    apply sSup_le
    rintro r ⟨ω, hω, rfl⟩
    have hω0 : ω = 0 := by
      apply Subtype.ext
      funext y
      by_contra hy
      have : y ∈ tsupport (ω : DifferentialForm (Euclid P) n) := subset_tsupport _ hy
      exact (hω.1 this).elim
    simp only [hω0, map_zero, ENNReal.ofReal_zero, le_refl]
  -- `ωₙ ∈ (0, ∞)`
  have hω0 : unitBallVolume n ≠ 0 :=
    (Metric.measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  -- the density ratio is eventually `< ofReal (θ + 1)` as `ρ ↓ 0`
  have hlt : ENNReal.ofReal θ < ENNReal.ofReal (θ + 1) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  obtain ⟨s₀, hs₀, hs₀ev⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1
    ((tendsto_order.1 hlimθ).2 _ hlt)
  -- hence `M_{B_ρ(x)}(T) ≤ ofReal (θ + 1) ωₙ ρⁿ` for `0 < ρ < s₀`
  have hmass : ∀ ρ : ℝ, 0 < ρ → ρ < s₀ →
      T.massOn (ball x ρ) ≤ ENNReal.ofReal (θ + 1) * (unitBallVolume n * ENNReal.ofReal (ρ ^ n)) := by
    intro ρ hρ hρs
    have h := hs₀ev ⟨hρ, hρs⟩
    have hb0 : unitBallVolume n * ENNReal.ofReal (ρ ^ n) ≠ 0 :=
      mul_ne_zero hω0 (ENNReal.ofReal_pos.2 (pow_pos hρ n)).ne'
    have hbtop : unitBallVolume n * ENNReal.ofReal (ρ ^ n) ≠ ∞ :=
      ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
    exact ((ENNReal.div_lt_iff (Or.inl hb0) (Or.inl hbtop)).1 h).le
  refine ⟨ENNReal.ofReal (θ + 1) * (unitBallVolume n * ENNReal.ofReal (R ^ n)),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top), ?_⟩
  have hsmall : ∀ᶠ j in atTop, lams j * R < s₀ := by
    have h0 : Tendsto (fun j => lams j * R) atTop (𝓝 0) := by
      simpa using hlim.mul_const R
    exact (tendsto_order.1 h0).2 s₀ hs₀
  filter_upwards [hsmall] with j hj
  have hlam := hlams j
  -- `η_j(B_{λⱼR}(x)) = B_R(0)`
  have himg : dilation x (lams j) '' ball x (lams j * R) = ball 0 R := by
    have hdil : ∀ y : Euclid P, dilation x (lams j) y = (lams j)⁻¹ • (y - x) := by
      intro y
      simp only [dilation, dilationCLM, FunLike.coe_smul, Pi.smul_apply,
        ContinuousLinearMap.coe_id', id_eq, smul_sub]
      abel
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_ball, dist_eq_norm] at hy
      rw [mem_ball, dist_zero_right, hdil, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hlam.le)]
      calc (lams j)⁻¹ * ‖y - x‖ < (lams j)⁻¹ * (lams j * R) :=
            mul_lt_mul_of_pos_left hy (inv_pos.2 hlam)
        _ = R := by field_simp
    · intro hz
      rw [mem_ball, dist_zero_right] at hz
      refine ⟨x + lams j • z, ?_, ?_⟩
      · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlam.le]
        exact mul_lt_mul_of_pos_left hz hlam
      · rw [hdil, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
  rw [← himg, (Submission.dtc_blowUp_scaling P n U U T x (lams j) hlam hU hn).1 (ball x (lams j * R))]
  calc ENNReal.ofReal ((lams j)⁻¹ ^ n) * T.massOn (ball x (lams j * R))
      ≤ ENNReal.ofReal ((lams j)⁻¹ ^ n) *
          (ENNReal.ofReal (θ + 1) * (unitBallVolume n * ENNReal.ofReal ((lams j * R) ^ n))) := by
        gcongr
        exact hmass _ (mul_pos hlam hR) hj
    _ = ENNReal.ofReal (θ + 1) * (unitBallVolume n * ENNReal.ofReal (R ^ n)) := by
        rw [mul_left_comm]
        congr 1
        rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hlam.ne', one_pow, one_mul]

## Key steps

1. R ≤ 0: B_R(0) = ∅, so the only admissible form is 0 and M_{B_R(0)}(S_j) = 0; take c = 0.
2. R > 0: HasMassDensity and 0 < ω_n < ∞ give s₀ > 0 with M_{B_ρ(x)}(T) ≤ ofReal(θ+1)·ω_n·ofReal(ρⁿ) for 0 < ρ < s₀.
3. η_j(B_{λ_jR}(x)) = B_R(0), so BU(1) gives M_{B_R(0)}(S_j) = ofReal(λ_j⁻¹ⁿ)·M_{B_{λ_jR}(x)}(T) once λ_jR < s₀.
4. ofReal(λ_j⁻¹ⁿ)·ofReal((λ_jR)ⁿ) = ofReal(Rⁿ), so M_{B_R(0)}(S_j) ≤ c := ofReal(θ+1)·ω_n·ofReal(Rⁿ) < ∞ for all large j.

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
