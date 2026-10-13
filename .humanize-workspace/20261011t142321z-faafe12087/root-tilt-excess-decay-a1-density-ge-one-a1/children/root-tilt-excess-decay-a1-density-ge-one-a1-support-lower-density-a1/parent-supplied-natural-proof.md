# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.density_ge_one-a1`
- Child DAG node: `root.tilt_excess_decay-a1.density_ge_one-a1.support_lower_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 3 and 5 of the parent proof of ted_density_ge_one (Simon, Introduction to GMT, Ch. 4, 3.11 and Remark 4.10(1)). Step 3 proves the upper-semicontinuity estimate through the inclusion B_t(z') ⊆ B_(t+eta)(z), followed by eta -> 0+ (continuity of mu from above on closed balls of finite measure) and then t -> 0+. Step 5 uses that an open mu-null set cannot meet spt mu. Here the two are combined in an equivalent pointwise form: every neighbourhood of a point of spt mu has positive measure, so it contains a point at which the a.e. estimate holds, and the estimate at such points transfers to y through the ball inclusion. The statement is for an arbitrary measure mu.

Notation.
- B_u(z) := closedBall z u (closed) and B°_u(z) := ball z u (open).
- M(u) := toReal(mu(B_u(y))), so M(u) >= 0.
- For x in R^(n+l), P(x) is the statement: if |x - y| < r, then omega <= (1 + c(t)) (toReal(mu(B_t(x)))/t^n) + c(t) for every t in (0, r].
- N := {x : P(x) fails}. The a.e. hypothesis says exactly mu(N) = 0 (ae_iff), as an outer-measure statement; no measurability of N is needed.

Other hypotheses: omega > 0, r > 0, y in spt mu, mu(B_(2r)(y)) < infinity, c(t) >= 0 for t in (0, r], and c(t) -> 0 as t -> 0+.

1. Finite masses near y. For u <= 2r, B_u(y) ⊆ B_(2r)(y). So mu(B_u(y)) <= mu(B_(2r)(y)) < infinity and mu(B_u(y)) = ofReal(M(u)).

2. Good points arbitrarily close to y. Let 0 < eta < r.
   - Since y is in spt mu, every neighbourhood of y has positive mu-measure (Measure.mem_support_iff_forall). B°_eta(y) is such a neighbourhood, so mu(B°_eta(y)) > 0.
   - If B°_eta(y) were contained in N, then mu(B°_eta(y)) <= mu(N) = 0 (measure_mono_null), a contradiction.
   - Hence there is x with |x - y| < eta and P(x). As eta < r, also |x - y| < r, so omega <= (1 + c(t)) (toReal(mu(B_t(x)))/t^n) + c(t) for every t in (0, r].

3. Comparison of balls. Fix t in (0, r] and u in (t, t + r). Put eta := u - t, so 0 < eta < r, and choose x as in step 2.
   - If |z - x| <= t, then |z - y| <= |z - x| + |x - y| < t + eta = u. So B_t(x) ⊆ B_u(y).
   - Since u < t + r <= 2r, step 1 gives mu(B_t(x)) <= mu(B_u(y)) < infinity. Hence toReal(mu(B_t(x))) <= M(u).
   - Because c(t) >= 0 we have 1 + c(t) > 0, and t^n > 0. So step 2 yields
     omega <= (1 + c(t)) (M(u)/t^n) + c(t) for every u in (t, t + r).

4. Letting u decrease to t.
   - The closed balls B_u(y), u > t, are measurable and increase with u. Their intersection over all u > t is B_t(y) (Metric.biInter_gt_closedBall). Moreover 2r > t and mu(B_(2r)(y)) < infinity.
   - By continuity of measure from above along u -> t+ (tendsto_measure_biInter_gt), mu(B_u(y)) -> mu(B_t(y)).
   - Since mu(B_t(y)) < infinity (step 1) and toReal is continuous at finite points (ENNReal.tendsto_toReal), M(u) -> M(t). Hence (1 + c(t)) (M(u)/t^n) + c(t) -> (1 + c(t)) (M(t)/t^n) + c(t) as u -> t+.
   - The inequality of step 3 holds on the right-neighbourhood (t, t + r) of t. The right-neighbourhood filter of t is a non-trivial filter on R. Passing to the limit u -> t+ (ge_of_tendsto) gives
     (*) omega <= (1 + c(t)) (M(t)/t^n) + c(t) for every t in (0, r].

5. Case epsilon >= 1. For every s > 0, (1 - epsilon)(omega s^n) <= 0, so ofReal((1 - epsilon)(omega s^n)) = 0 <= mu(B_s(y)). Thus the inequality holds for all s > 0, in particular eventually as s -> 0+.

6. Case 0 < epsilon < 1.
   (i) Put gamma := epsilon omega / (1 + omega) > 0, so gamma (1 + omega) = epsilon omega.
   (ii) Since c(s) -> 0 as s -> 0+ and (0, r) is a right-neighbourhood of 0, eventually as s -> 0+ we have both c(s) < gamma and s in (0, r).
   (iii) Fix such an s and put q := M(s)/s^n >= 0. By (*) with t = s, q >= 0 and 0 <= c(s) < gamma,
     omega <= (1 + c(s)) q + c(s) <= (1 + gamma) q + gamma.
   (iv) Suppose q < (1 - epsilon) omega. Then (1 + gamma) q < (1 + gamma)(1 - epsilon) omega, hence
     omega < (1 + gamma)(1 - epsilon) omega + gamma
           = (1 - epsilon) omega + gamma (1 + omega) - gamma epsilon omega
           = (1 - epsilon) omega + epsilon omega - gamma epsilon omega
           = omega - gamma epsilon omega.
     This is impossible, since gamma epsilon omega > 0.
   (v) Therefore q >= (1 - epsilon) omega, i.e. M(s) = q s^n >= (1 - epsilon) omega s^n.
   (vi) As s < r < 2r, step 1 gives mu(B_s(y)) = ofReal(M(s)) >= ofReal((1 - epsilon)(omega s^n)), by monotonicity of ofReal.

7. Conclusion. By steps 5 and 6, for every epsilon > 0 the inequality ofReal((1 - epsilon)(omega s^n)) <= mu(B_s(y)) holds for all s in a right-neighbourhood of 0, i.e. eventually along s -> 0+ (the filter 𝓝[>] 0).

Remark (use in the parent; not part of the proof). The parent applies this child with mu = V.weight, y in spt V ∩ B°_rho(0) (so y in spt mu), omega = omega_n, r = (rho - |y|)/8 and c(t) = A (t/r)^(1 - n/p), A = e^(Lambda/2) Lambda / 2. Then mu(B_(2r)(y)) < infinity because B_(2r)(y) is a compact subset of B_rho(0) ⊆ U, and the a.e. estimate is supplied by ted_dge1_density_le_monotone_bound, ted_lp_monotonicity and ted_tangent_plane_facts (3) together with theta >= 1 mu-a.e.

Remark (verified Lean realization; not part of the mathematical argument). The following proof compiled with Lean v4.35.0-rc3 / Mathlib 25730c7c inside `namespace GMT.Ch05` / `namespace Submission`, placed before `main_theorem` in a copy of GMT/Ch05/Submission.lean, i.e. in the scope of the frozen contract's `open` commands. `#print axioms` reports only propext, Classical.choice and Quot.sound, and the comparator module generated by verifier/gmt-compare.py child_modules (`exact Submission.ted_dge1_support_density_lower_bound`) compiles:

```lean
theorem ted_dge1_support_density_lower_bound : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (ω r : ℝ) (c : ℝ → ℝ), 0 < ω → 0 < r → y ∈ μ.support → μ (closedBall y (2 * r)) < ⊤ → (∀ t : ℝ, 0 < t → t ≤ r → 0 ≤ c t) → Tendsto c (𝓝[>] 0) (𝓝 0) → (∀ᵐ x ∂μ, x ∈ ball y r → ∀ t : ℝ, 0 < t → t ≤ r → ω ≤ (1 + c t) * ((μ (closedBall x t)).toReal / t ^ n) + c t) → ∀ ε : ℝ, 0 < ε → ∀ᶠ s in 𝓝[>] (0 : ℝ), ENNReal.ofReal ((1 - ε) * (ω * s ^ n)) ≤ μ (closedBall y s) := by
  intro n ℓ μ y ω r c hω hr hy hfin hc0 hc hae ε hε
  have hfin' : ∀ u : ℝ, u ≤ 2 * r → μ (closedBall y u) ≠ ⊤ := fun u hu =>
    (lt_of_le_of_lt (measure_mono (closedBall_subset_closedBall hu)) hfin).ne
  have hA : ∀ t : ℝ, 0 < t → t ≤ r →
      ω ≤ (1 + c t) * ((μ (closedBall y t)).toReal / t ^ n) + c t := by
    intro t ht htr
    have hct : 0 ≤ c t := hc0 t ht htr
    have htn : 0 < t ^ n := pow_pos ht n
    have hu : ∀ u : ℝ, t < u → u < t + r →
        ω ≤ (1 + c t) * ((μ (closedBall y u)).toReal / t ^ n) + c t := by
      intro u htu hut
      have hη : 0 < u - t := sub_pos.mpr htu
      have hpos : 0 < μ (ball y (u - t)) :=
        (Measure.mem_support_iff_forall y).mp hy _ (ball_mem_nhds y hη)
      obtain ⟨x, hxb, hx⟩ : ∃ x ∈ ball y (u - t), (x ∈ ball y r → ∀ t : ℝ, 0 < t → t ≤ r →
          ω ≤ (1 + c t) * ((μ (closedBall x t)).toReal / t ^ n) + c t) := by
        by_contra hcon
        have hsub : ball y (u - t) ⊆ {x | ¬ (x ∈ ball y r → ∀ t : ℝ, 0 < t → t ≤ r →
            ω ≤ (1 + c t) * ((μ (closedBall x t)).toReal / t ^ n) + c t)} := by
          intro x hx hgood
          exact hcon ⟨x, hx, hgood⟩
        exact absurd (measure_mono_null hsub (ae_iff.mp hae)) hpos.ne'
      have hxr : x ∈ ball y r := ball_subset_ball (by linarith) hxb
      have h1 := hx hxr t ht htr
      have hsub : closedBall x t ⊆ closedBall y u := by
        intro z hz
        rw [mem_closedBall] at hz ⊢
        rw [mem_ball] at hxb
        linarith [dist_triangle z x y]
      have hle : (μ (closedBall x t)).toReal ≤ (μ (closedBall y u)).toReal :=
        ENNReal.toReal_mono (hfin' u (by linarith)) (measure_mono hsub)
      have : (1 + c t) * ((μ (closedBall x t)).toReal / t ^ n) ≤
          (1 + c t) * ((μ (closedBall y u)).toReal / t ^ n) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact div_le_div_of_nonneg_right hle htn.le
      linarith
    have hlim : Tendsto (fun u => (μ (closedBall y u)).toReal) (𝓝[>] t)
        (𝓝 ((μ (closedBall y t)).toReal)) := by
      have h1 := tendsto_measure_biInter_gt (μ := μ) (s := fun u => closedBall y u) (a := t)
        (fun u _ => measurableSet_closedBall.nullMeasurableSet)
        (fun i j _ hij => closedBall_subset_closedBall hij)
        ⟨2 * r, by linarith, hfin.ne⟩
      rw [biInter_gt_closedBall] at h1
      exact (ENNReal.tendsto_toReal (hfin' t (by linarith))).comp h1
    have hlim2 : Tendsto (fun u => (1 + c t) * ((μ (closedBall y u)).toReal / t ^ n) + c t)
        (𝓝[>] t) (𝓝 ((1 + c t) * ((μ (closedBall y t)).toReal / t ^ n) + c t)) :=
      ((hlim.div_const _).const_mul _).add_const _
    apply ge_of_tendsto hlim2
    filter_upwards [Ioo_mem_nhdsGT (by linarith : t < t + r)] with u hu'
    exact hu u hu'.1 hu'.2
  rcases le_or_gt 1 ε with h1 | h1
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : (0:ℝ) < s := hs
    have : (1 - ε) * (ω * s ^ n) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    rw [ENNReal.ofReal_of_nonpos this]
    exact zero_le
  · set γ := ε * ω / (1 + ω) with hγ_def
    have hγ : 0 < γ := by positivity
    have hγ' : γ * (1 + ω) = ε * ω := by rw [hγ_def]; field_simp
    have hev1 : ∀ᶠ s in 𝓝[>] (0:ℝ), c s < γ := hc.eventually (gt_mem_nhds hγ)
    have hev2 : ∀ᶠ s in 𝓝[>] (0:ℝ), s ∈ Ioo 0 r := Ioo_mem_nhdsGT hr
    filter_upwards [hev1, hev2] with s hcs hs
    have hA' := hA s hs.1 hs.2.le
    have hsn : 0 < s ^ n := pow_pos hs.1 n
    have hcs0 : 0 ≤ c s := hc0 s hs.1 hs.2.le
    set q := (μ (closedBall y s)).toReal / s ^ n with hq_def
    have hq : 0 ≤ q := div_nonneg ENNReal.toReal_nonneg hsn.le
    have h2 : ω ≤ (1 + γ) * q + γ := by nlinarith
    have key : (1 - ε) * ω ≤ q := by
      by_contra hlt
      push Not at hlt
      have h3 : (1 + γ) * q < (1 + γ) * ((1 - ε) * ω) := mul_lt_mul_of_pos_left hlt (by linarith)
      have h4 : 0 < γ * ε * ω := by positivity
      nlinarith [hγ']
    have key2 : (1 - ε) * (ω * s ^ n) ≤ (μ (closedBall y s)).toReal := by
      have h5 : (μ (closedBall y s)).toReal = q * s ^ n := by
        rw [hq_def, div_mul_cancel₀ _ hsn.ne']
      rw [h5]
      nlinarith [mul_le_mul_of_nonneg_right key hsn.le]
    rw [← ENNReal.ofReal_toReal (hfin' s (by linarith [hs.2]))]
    exact ENNReal.ofReal_le_ofReal key2
```

## Key steps

1. Masses mu(B_u(y)) with u <= 2r are finite.
2. Since y is in spt mu, each open ball B°_eta(y) has positive measure, so it contains a point x where the a.e. estimate holds.
3. B_t(x) ⊆ B_(t+eta)(y) transfers the estimate to omega <= (1 + c(t)) M(t+eta)/t^n + c(t).
4. Continuity of mu from above on closed balls of finite measure, as eta -> 0+, gives omega <= (1 + c(t)) M(t)/t^n + c(t) for t in (0, r].
5. With gamma = epsilon omega/(1 + omega) and c(s) < gamma for small s, M(s) >= (1 - epsilon) omega s^n; the case epsilon >= 1 is trivial.

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean (both identical; sha256 c966f51e...)`
- `timeout 300 rg -n 'ted_dge1|density_le_monotone_bound|support_density_lower_bound|ted_density_ge_one' <snapshot>/project (no match)`
- `timeout 1500 rg -l -i 'varifold' <snapshot>/mathlib/Mathlib (no match)`
- `rg -n 'theorem mem_support_iff_forall|lemma mem_support_iff_forall' MeasureTheory/Measure/Support.lean (in <snapshot>/mathlib/Mathlib)`
- `rg -n 'theorem tendsto_measure_biInter_gt' MeasureTheory/Measure/Continuity.lean`
- `rg -n 'theorem biInter_gt_closedBall|theorem squeeze_zero.|lemma squeeze_zero.' Topology/MetricSpace/Pseudo/Lemmas.lean`
- `rg -n 'theorem tendsto_toReal ' Topology/Instances/ENNReal/Lemmas.lean`
- `rg -n 'toReal_div\b|lemma toReal_mono\b|theorem toReal_mono\b|ofReal_of_nonpos\b|theorem ofReal_toReal\b|rpow_lt_top_iff_of_pos|theorem mul_lt_top_iff\b' Basic/ENNReal Data/ENNReal Analysis/SpecialFunctions/Pow/NNReal.lean`
- `rg -n 'theorem Filter.Tendsto.rpow_const|theorem zero_rpow ' Analysis/SpecialFunctions/Pow/Continuity.lean Analysis/SpecialFunctions/Pow/Real.lean`
- `rg -n 'theorem measure_mono_null' MeasureTheory/OuterMeasure/Basic.lean; rg -n 'theorem ae_iff' MeasureTheory/OuterMeasure/AE.lean`
- `rg -n 'theorem withDensity_apply |theorem restrict_restrict |theorem lintegral_mono_set ' MeasureTheory/Measure/WithDensity.lean MeasureTheory/Measure/Restrict.lean MeasureTheory/Integral/Lebesgue/Basic.lean`
- `rg -n 'theorem le_of_tendsto |theorem Gamma_pos_of_pos|theorem rpow_le_rpow ' Topology/Order Analysis/SpecialFunctions/Gamma/Basic.lean Analysis/SpecialFunctions/Pow/Real.lean`
- `ls .lake/packages/simongmt/Poincare/SimonGMT/Chapter04; rg -n 'theorem one_le_stationaryDensityReal_of_mem_support_lp|theorem upperSemicontinuousOn_stationaryDensityReal_lp|theorem scaledLpMeanCurvature_mono_ball|def stationaryDensityReal' .lake/packages/simongmt/Poincare/SimonGMT/Chapter04`
- `python3 -I scan of dag.json: lean_name, lean_statement and status of root.tilt_excess_decay-a1.{density_ge_one,lp_monotonicity,tangent_plane_facts}-a1 and root.affine_approximation-a1.density_ge_one-a1{,.monotone_density_bound-a1,.support_lower_density-a1}; nodes whose lean_name is ted_dge1_density_le_monotone_bound or ted_dge1_support_density_lower_bound (none); duplicate lean_names (none)`
- `grep -n 'def _solve_children|def _existing_lean_name_problem|max_nodes' /runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/runtime.py; max_nodes in .humanize/swarm-configs/1625d2a705464ec1a08f788eb20c9abc.json (200) and 7e4cfed8fb4c4d699cb2d2db6572f1b6.json (1000)`
- `sha256 of parent-supplied natural proof (handoff subproblem.natural_proof) = a1f701e37437e4bfbc04bf2851fcb40e0bbe4315e73ef440b4318581532b4bc1, equal to decomposition-scope-v1.json proof_sha256`
- `python3 -I /tmp/claude-1000/ted-dge1-a3/scripts/{extract.py,gen.py,mksrc.py} (frozen types from decomposition-v1.json/dag.json; verifier gmt-compare.py contract_scope + child_modules; lean_contract.py validate_lean_statement)`
- `scripts/runlean.sh '' src{1,2,3} -o b{1,2,3}/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean; scripts/runlean.sh b1 gen/<name>__NodeChallenge.lean (3 types); scripts/runlean.sh b2 gen/ted_dge1_*__NodeSolution.lean, checks/AxChildren.lean, checks/Assembly.lean; scripts/runlean.sh b3 gen/ted_density_ge_one__NodeSolution.lean, checks/AxParent.lean`
- `sed -n 318,365p book/chapter-04.txt; sed -n 518,570p book/chapter-04.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Density.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-density-ge-one-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-density-ge-one-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-density-ge-one-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-density-ge-one-a1/decomposition-scope-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-tangent-plane-facts-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/swarm-configs/1625d2a705464ec1a08f788eb20c9abc.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/swarm-configs/7e4cfed8fb4c4d699cb2d2db6572f1b6.json`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/tmp/claude-1000/ted-dge1-a3/scripts/extract.py`
- `/tmp/claude-1000/ted-dge1-a3/scripts/gen.py`
- `/tmp/claude-1000/ted-dge1-a3/scripts/mksrc.py`
- `/tmp/claude-1000/ted-dge1-a3/scripts/runlean.sh`
- `/tmp/claude-1000/ted-dge1-a3/checks/Assembly.lean`
- `/tmp/claude-1000/ted-dge1-a3/checks/AxChildren.lean`
- `/tmp/claude-1000/ted-dge1-a3/checks/AxParent.lean`
- `/tmp/claude-1000/ted-dge1-a3/logs`

Pins and contract. Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical. The supplied proof is unchanged since v1 (sha256 a1f701e3...).

No-match searches. The snapshot project contains no declaration named ted_dge1_*, density_le_monotone_bound, support_density_lower_bound or ted_density_ge_one. Mathlib has no varifold file.

Names. dag.json (220 nodes) has no node named ted_dge1_density_le_monotone_bound or ted_dge1_support_density_lower_bound, and no duplicate lean_name. The twins aal_dge1_density_le_monotone_bound (rlcr-lean) and aal_dge1_support_density_lower_bound (decomposing) have byte-identical types but are not accepted checkpoints. Fresh names are therefore required, and both proposed names are free.

Mathlib lemmas used by the child proofs and the assembly, located in the snapshot:
- Measure.mem_support_iff_forall (Support.lean:75).
- tendsto_measure_biInter_gt (Continuity.lean:266).
- Metric.biInter_gt_closedBall and squeeze_zero' (Pseudo/Lemmas.lean:100, :32).
- ENNReal.tendsto_toReal (Instances/ENNReal/Lemmas.lean:102).
- ENNReal.toReal_div (Basic/ENNReal/Inv.lean:977), toReal_mono (Basic/ENNReal/Real.lean:67) and ofReal_toReal (Basic/ENNReal/Basic.lean:248).
- ENNReal.mul_lt_top_iff (Operations.lean:211) and ENNReal.rpow_lt_top_iff_of_pos (Pow/NNReal.lean:602).
- Filter.Tendsto.rpow_const (Pow/Continuity.lean:246), Real.zero_rpow (Pow/Real.lean:128) and Real.rpow_le_rpow (Pow/Real.lean:549).
- measure_mono_null (OuterMeasure/Basic.lean:54) and ae_iff (OuterMeasure/AE.lean:134).
- withDensity_apply (WithDensity.lean:44), Measure.restrict_restrict (Restrict.lean:205) and lintegral_mono_set (Lebesgue/Basic.lean:98).
- le_of_tendsto (OrderClosed.lean:133) and Real.Gamma_pos_of_pos (Gamma/Basic.lean:443).

SimonGMT. Chapter04 (Density.lean:57 stationaryDensityReal; LpDensity.lean:125 scaledLpMeanCurvature_mono_ball) is stated for the strengthened Chapter04.RectifiableVarifold. The chapter README says it needs a bridge via Ch. 3, 1.9, and the queried u.s.c. and lower-density names have no match. Nothing from it is used, since both children are abstract measure lemmas.

Runtime. The v1 worker config has max_nodes = 200 and the current config has 1000. runtime.py's _solve_children node bound explains why the audited v1 split was not activated and why the same two new ids now fit.

Lean checks, fresh in /tmp/claude-1000/ted-dge1-a3:
- All three NodeChallenge modules elaborate against a contract-only Submission.
- Both child proofs compile with only standard axioms, and their NodeSolution modules compile.
- The assembly with the frozen sibling types as hypotheses proves the frozen ted_density_ge_one type with axioms propext, Classical.choice and Quot.sound.
- End to end, with sorry placeholders for the two siblings, the parent's NodeSolution module compiles.
