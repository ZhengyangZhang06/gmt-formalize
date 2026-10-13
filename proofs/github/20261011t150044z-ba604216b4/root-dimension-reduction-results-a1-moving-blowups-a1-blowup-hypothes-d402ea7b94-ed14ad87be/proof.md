# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.blowup_hypotheses-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.blowup_hypotheses-a1.moving_mass_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Part II.4 of the selected node's supplied proof (Simon 7.3.1, proof, chapter-07.txt lines 325–331: the scaling identity (ωₙRⁿ)⁻¹M_{B_R(0)}(η_{x,λ_j#}T) = (ωₙλ_jⁿRⁿ)⁻¹M_{B_{λ_jR}(x)}(T) together with the monotonicity formula gives sup_j M_{B_R(0)}(η_{x,λ_j#}T) < ∞; here the centres x_j move). Dependencies (siblings): mass_and_support = Submission.dor_imrep_massOn_eq_measure_and_support (MR: for U open and an IMRep R₀ representing T, M_W(T) = R₀.measure(W) for every open W) and blowup_mass_scaling = Submission.dtc_blowUp_massOn_image (MS: for λ > 0 and every W, M_{η_{a,λ}(W)}(blowUp T a λ) = ofReal((λ⁻¹)ⁿ)·M_W(T)).
Notation: λ_j := lams j > 0, x_j := xs j, η_j := dilation x_j λ_j (η_j(y) = λ_j⁻¹(y − x_j)), S_j := blowUp T x_j λ_j, B_s(y) := ball y s; 'for all large j' means eventually in atTop.
1. (Radius.) U is open and x ∈ U, so there is ε > 0 with B_ε(x) ⊆ U; put r := ε/3 > 0. Then K := closedBall(x, 2r) ⊆ B_ε(x) ⊆ U, and K is compact (closed balls of ℝ^P are compact).
2. (Monotonicity.) The hypothesis applied to K gives Λ ≥ 0 such that for all y ∈ ℝ^P and s ∈ ℝ with closedBall(y, s) ⊆ K, the function f_y(ρ) := ofReal(e^{Λρ}/ρⁿ)·M_{B_ρ(y)}(T) ∈ [0, ∞] is monotone (nondecreasing) on (0, s).
3. (Finite mass near x.) T is integer multiplicity; let R₀ = (M, θ, ξ) be an IMRep representing T in U. By MR (U and B_{2r}(x) open), M_{B_{2r}(x)}(T) = R₀.measure(B_{2r}(x)) ≤ R₀.measure(K) (B_{2r}(x) ⊆ K). By definition R₀.measure = (Hⁿ⌞M).withDensity θ, so, K being Borel, R₀.measure(K) = ∫_K θ d(Hⁿ⌞M) = ∫_{M∩K} θ dHⁿ (withDensity_apply, Measure.restrict_restrict), which is finite by the local integrability of θ (R₀.locallyIntegrable_mult, K compact ⊆ U). Hence M_{B_{2r}(x)}(T) < ∞ and c₁ := ofReal(e^{Λr}(2/r)ⁿ)·M_{B_{2r}(x)}(T) is finite.
4. (Uniform density bound near x.) Claim: if |y − x| < r and 0 < ρ < r/2, then M_{B_ρ(y)}(T) ≤ ofReal(ρⁿ)·c₁. (a) closedBall(y, r) ⊆ K, since |z − y| ≤ r gives |z − x| ≤ |z − y| + |y − x| < 2r. By step 2 with s := r, f_y is monotone on (0, r); as ρ and r/2 lie in (0, r) and ρ ≤ r/2, f_y(ρ) ≤ f_y(r/2) = ofReal(e^{Λr/2}/(r/2)ⁿ)·M_{B_{r/2}(y)}(T). (b) B_{r/2}(y) ⊆ B_{2r}(x) (|z − x| < r/2 + r), so M_{B_{r/2}(y)}(T) ≤ M_{B_{2r}(x)}(T) (massOn is monotone in the set, GeometricCurrentOn.massOn_mono); and e^{Λr/2}/(r/2)ⁿ = e^{Λr/2}(2/r)ⁿ ≤ e^{Λr}(2/r)ⁿ since Λ ≥ 0 and r > 0. Hence f_y(r/2) ≤ c₁. (c) Since Λρ ≥ 0, e^{Λρ} ≥ 1, so ρ^{−n} ≤ e^{Λρ}/ρⁿ and ofReal(ρ^{−n})·M_{B_ρ(y)}(T) ≤ f_y(ρ) ≤ c₁. Multiplying by ofReal(ρⁿ) and using ofReal(ρⁿ)·ofReal(ρ^{−n}) = ofReal(1) = 1 (ρ > 0) gives M_{B_ρ(y)}(T) ≤ ofReal(ρⁿ)·c₁.
5. (The constant.) Let R ∈ ℝ, put R′ := max(R, 1) > 0 and c := ofReal(R′ⁿ)·c₁, which is finite. (Using R′ instead of R also covers R ≤ 0, where alternatively B_R(0) = ∅ and M_∅ = 0.)
6. (Large j.) Since x_j → x and λ_jR′ → 0·R′ = 0, for all large j both |x_j − x| < r and λ_jR′ < r/2 hold. Fix such j. (a) η_j(B_{λ_jR′}(x_j)) = B_{R′}(0): if |y − x_j| < λ_jR′ then |η_j(y)| = λ_j⁻¹|y − x_j| < R′; conversely, for |z| < R′ the point y := x_j + λ_jz satisfies |y − x_j| = λ_j|z| < λ_jR′ and η_j(y) = λ_j⁻¹(λ_jz) = z. (b) Since B_R(0) ⊆ B_{R′}(0), monotonicity of massOn, MS with W := B_{λ_jR′}(x_j), and step 4 with y := x_j and ρ := λ_jR′ ∈ (0, r/2) give M_{B_R(0)}(S_j) ≤ M_{B_{R′}(0)}(S_j) = M_{η_j(W)}(S_j) = ofReal((λ_j⁻¹)ⁿ)·M_W(T) ≤ ofReal((λ_j⁻¹)ⁿ)·ofReal((λ_jR′)ⁿ)·c₁ = ofReal((λ_j⁻¹)ⁿ(λ_jR′)ⁿ)·c₁ = ofReal(R′ⁿ)·c₁ = c.
7. (Conclusion.) For every R ∈ ℝ, c ≠ ∞ and M_{B_R(0)}(blowUp T x_j λ_j) ≤ c for all large j. Minimality was not used, and for n = 0 all powers equal 1 and the argument is unchanged. ∎

Lean reference implementation (kernel-checked during this decomposition with Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b366308, after import GMT.Ch07.Submission in the contract scope `namespace GMT.Ch07`, with the contract's opens; the two dependencies were present as declarations of their exact frozen types; `#print axioms` of the conditional version shows only propext, Classical.choice, Quot.sound):

theorem Submission.dimred_mbl_bh_moving_blowUp_mass_bound : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity T → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (y : Euclid P) (R : ℝ), closedBall y R ⊆ K → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) → ∀ (x : Euclid P) (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → ∀ R : ℝ, ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ᶠ j in atTop, (blowUp T (xs j) (lams j) (hlams j).ne').massOn (ball 0 R) ≤ c := by
  intro P n U T hU hIM hmon x xs lams hlams hxU hxs hlam0 R
  -- `η_{a,λ}(y) = λ⁻¹ • (y - a)`
  have hdil : ∀ (a : Euclid P) (lam : ℝ) (y : Euclid P), dilation a lam y = lam⁻¹ • (y - a) := by
    intro a lam y
    simp only [dilation, dilationCLM, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.coe_id', id_eq, smul_sub]
    abel
  -- Step 0: a radius `r` with `closedBall x (2r) ⊆ U`
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hxU
  set r := ε / 3 with hr_def
  have hr : 0 < r := by positivity
  have hK : closedBall x (2 * r) ⊆ U := by
    intro y hy
    apply hεU
    rw [mem_ball]
    rw [mem_closedBall] at hy
    linarith
  have hKc : IsCompact (closedBall x (2 * r)) := isCompact_closedBall x (2 * r)
  -- Step 1: monotonicity on `K = closedBall x (2r)`
  obtain ⟨Λ, hΛ, hmono⟩ := hmon _ hKc hK
  -- Step 2: `M_{B_{2r}(x)}(T) < ∞`
  obtain ⟨Rep, hRep⟩ := hIM
  have hfin : T.massOn (ball x (2 * r)) ≠ ∞ := by
    rw [(Submission.dor_imrep_massOn_eq_measure_and_support P n U T Rep hU hRep).1 _ isOpen_ball]
    have h1 : Rep.measure (ball x (2 * r)) ≤ Rep.measure (closedBall x (2 * r)) :=
      measure_mono ball_subset_closedBall
    have h2 : Rep.measure (closedBall x (2 * r)) =
        ∫⁻ y in Rep.carrier ∩ closedBall x (2 * r), (Rep.mult y : ℝ≥0∞) ∂μHE[n] := by
      unfold IMRep.measure
      rw [withDensity_apply _ measurableSet_closedBall,
        Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    have h3 := Rep.locallyIntegrable_mult _ hKc hK
    rw [← h2] at h3
    exact ne_top_of_le_ne_top h3 h1
  -- Step 3: the constant `c₁`
  set c₁ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (Λ * r) * (2 / r) ^ n) * T.massOn (ball x (2 * r))
    with hc₁_def
  have hc₁ : c₁ ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  -- Step 4: `M_{B_ρ(y)}(T) ≤ ρⁿ c₁` for `|y - x| < r`, `0 < ρ < r/2`
  have hkey : ∀ y : Euclid P, dist y x < r → ∀ ρ : ℝ, 0 < ρ → ρ < r / 2 →
      T.massOn (ball y ρ) ≤ ENNReal.ofReal (ρ ^ n) * c₁ := by
    intro y hy ρ hρ hρr
    have hKy : closedBall y r ⊆ closedBall x (2 * r) := by
      intro z hz
      rw [mem_closedBall] at hz ⊢
      linarith [dist_triangle z y x]
    have hρmem : ρ ∈ Ioo 0 r := ⟨hρ, by linarith⟩
    have hr2mem : r / 2 ∈ Ioo 0 r := ⟨by positivity, by linarith⟩
    have hle := hmono y r hKy hρmem hr2mem hρr.le
    have hball : ball y (r / 2) ⊆ ball x (2 * r) := by
      intro z hz
      rw [mem_ball] at hz ⊢
      linarith [dist_triangle z y x]
    have hM : T.massOn (ball y (r / 2)) ≤ T.massOn (ball x (2 * r)) := T.massOn_mono hball
    have hcoef : ENNReal.ofReal (Real.exp (Λ * (r / 2)) / (r / 2) ^ n) ≤
        ENNReal.ofReal (Real.exp (Λ * r) * (2 / r) ^ n) := by
      apply ENNReal.ofReal_le_ofReal
      rw [div_eq_mul_inv, ← inv_pow, inv_div]
      gcongr
      nlinarith
    have h1 : ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball y ρ) ≤ c₁ :=
      hle.trans (mul_le_mul' hcoef hM)
    have hexp : 1 ≤ Real.exp (Λ * ρ) := Real.one_le_exp (by positivity)
    have h2 : ENNReal.ofReal ((ρ ^ n)⁻¹) * T.massOn (ball y ρ) ≤ c₁ := by
      refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl) h1
      rw [div_eq_mul_inv]
      have : 0 < (ρ ^ n)⁻¹ := by positivity
      nlinarith
    calc T.massOn (ball y ρ)
        = ENNReal.ofReal (ρ ^ n) * (ENNReal.ofReal ((ρ ^ n)⁻¹) * T.massOn (ball y ρ)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (ρ ^ n) * c₁ := mul_le_mul' le_rfl h2
  -- Step 5: rescale
  set R' := max R 1 with hR'_def
  have hR' : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨ENNReal.ofReal (R' ^ n) * c₁, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc₁, ?_⟩
  have hev1 : ∀ᶠ j in atTop, dist (xs j) x < r := Metric.tendsto_nhds.1 hxs r hr
  have hev2 : ∀ᶠ j in atTop, lams j * R' < r / 2 := by
    have h0 : Tendsto (fun j => lams j * R') atTop (𝓝 0) := by
      simpa using hlam0.mul_const R'
    exact (tendsto_order.1 h0).2 (r / 2) (by positivity)
  filter_upwards [hev1, hev2] with j hj1 hj2
  have hlam := hlams j
  have himg : dilation (xs j) (lams j) '' ball (xs j) (lams j * R') = ball 0 R' := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_ball, dist_zero_right, hdil, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hlam.le),
        ← dist_eq_norm]
      rw [mem_ball] at hy
      calc (lams j)⁻¹ * dist y (xs j) < (lams j)⁻¹ * (lams j * R') :=
            mul_lt_mul_of_pos_left hy (inv_pos.2 hlam)
        _ = R' := by field_simp
    · intro hz
      refine ⟨xs j + lams j • z, ?_, ?_⟩
      · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlam.le]
        rw [mem_ball, dist_zero_right] at hz
        exact mul_lt_mul_of_pos_left hz hlam
      · rw [hdil, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
  calc (blowUp T (xs j) (lams j) (hlams j).ne').massOn (ball 0 R)
      ≤ (blowUp T (xs j) (lams j) (hlams j).ne').massOn (ball 0 R') :=
        GeometricCurrentOn.massOn_mono _ (ball_subset_ball (le_max_left _ _))
    _ = (blowUp T (xs j) (lams j) (hlams j).ne').massOn
          (dilation (xs j) (lams j) '' ball (xs j) (lams j * R')) := by rw [himg]
    _ = ENNReal.ofReal ((lams j)⁻¹ ^ n) * T.massOn (ball (xs j) (lams j * R')) :=
        Submission.dtc_blowUp_massOn_image P n U T (xs j) (lams j) (hlams j) _
    _ ≤ ENNReal.ofReal ((lams j)⁻¹ ^ n) * (ENNReal.ofReal ((lams j * R') ^ n) * c₁) :=
        mul_le_mul' le_rfl (hkey _ hj1 _ (by positivity) hj2)
    _ = ENNReal.ofReal (R' ^ n) * c₁ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
          inv_mul_cancel_left₀ hlam.ne']

## Key steps

1. Fix r with closedBall(x, 2r) ⊆ U; the monotonicity hypothesis on K = closedBall(x, 2r) gives Λ ≥ 0.
2. MR and the local integrability of the multiplicity give M_{B_{2r}(x)}(T) < ∞, hence the finite constant c₁ = ofReal(e^{Λr}(2/r)ⁿ)M_{B_{2r}(x)}(T).
3. Monotonicity between ρ and r/2 on balls centred at y with |y − x| < r gives M_{B_ρ(y)}(T) ≤ ofReal(ρⁿ)c₁ for 0 < ρ < r/2.
4. For large j, η_j(B_{λ_jR′}(x_j)) = B_{R′}(0), and mass scaling gives M_{B_R(0)}(S_j) ≤ ofReal(λ_j^{−n})ofReal((λ_jR′)ⁿ)c₁ = ofReal(R′ⁿ)c₁ with R′ = max(R, 1).

## Reference use

### local-project

Queries:
- `cat SNAP/manifest.json; git -C SNAP/project rev-parse HEAD; git -C SNAP/mathlib rev-parse HEAD; cmp SNAP/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean`
- `rg -n 'def dilation|def blowUp|def IsEmbeddedSubmanifold|def IsMinimizingIn|def BoundaryVanishes' SNAP/project/GMT/Ch07/Contract.lean`
- `rg -n 'def toOpenPartialHomeomorph|def localInverse|theorem to_localInverse|theorem mem_toOpenPartialHomeomorph_source' SNAP/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/*.lean`
- `rg -n 'theorem OpenPartialHomeomorph.contDiffAt_symm' SNAP/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `rg -n 'norm_image_sub_le_of_norm_fderiv_le' SNAP/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `rg -n 'theorem starProjection_norm_le' SNAP/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean; rg -n 'noncomputable def ofInjective' SNAP/mathlib/Mathlib/Algebra/Module/Submodule/Equiv.lean`
- `rg -n 'theorem withDensity_apply|theorem restrict_restrict' SNAP/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean SNAP/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n 'Homeomorph.smulOfNeZero' SNAP/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean`
- `rg -ln 'retraction' SNAP/project/GMT (no match)`
- `sed -n / grep -n on simongmt Chapter06 AffineCurrentPushforward.lean (affinePullbackForm, affinePushforward_apply, boundary_affinePushforward), Mass.lean (massOn, massOn_mono), Currents.lean (GeometricCurrentOn.ext, zero_apply)`
- `python3 scans of RUN/dag.json: accepted declarations mentioning blowUp, dilation, IsEmbeddedSubmanifold or retraction; lean_name collisions for dimred_mbl_bh_* (none); status of dtc_bc_local_retraction and of the dtc_bc_blowUp_hypotheses subtree (not accepted)`
- `git show a8aa184/f64597f/17c63f2/d49dda9:GMT/Ch07/Submission.lean | grep -n 'theorem Submission.<reused name> '`
- `sed -n 160,185p and 285,345p book/chapter-07.txt (Remark 7.2.5, Theorem 7.3.1 and its proof)`
- `lake env lean on /tmp/bh_split/{Elab,AssemblyCond,N1check,N3check,Concrete}.lean and /tmp/bh_split/final/Final.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Module/Submodule/Equiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-blowup-hypotheses-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-retraction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/tmp/bh_split/final/Final.lean`

Pins match (project b4d606d, Mathlib 25730c7c, SimonGMT 2b366308 in the lake packages), and Submission.lean is byte-identical to the snapshot's frozen contract. The snapshot supplies everything the children need. From Mathlib: the C¹ inverse function theorem (ContDiffAt.toOpenPartialHomeomorph, localInverse, to_localInverse, OpenPartialHomeomorph.contDiffAt_symm), the mean value inequality (Convex.norm_image_sub_le_of_norm_fderiv_le), starProjection_norm_le, LinearEquiv.ofInjective, withDensity_apply, Measure.restrict_restrict and Homeomorph.smulOfNeZero. From SimonGMT: the affine pull-back and push-forward of currents, massOn and massOn_mono. There is no local retraction onto submanifolds in the project ('retraction' in project/GMT: no match) or among accepted DAG declarations, so local_retraction is a genuine new obligation. Accepted DAG declarations reused with identical types: dtc_blowUp_isMinimizingIn, dtc_blowUp_algebra, dtc_blowUp_massOn_image and dor_imrep_massOn_eq_measure_and_support, each verified verbatim in its commit. The analogous fixed-centre nodes (dtc_bc_blowUp_hypotheses and its children, dtc_bc_local_retraction) are not accepted and cannot be shared. All child types elaborate, and the assembly proves the selected type.
