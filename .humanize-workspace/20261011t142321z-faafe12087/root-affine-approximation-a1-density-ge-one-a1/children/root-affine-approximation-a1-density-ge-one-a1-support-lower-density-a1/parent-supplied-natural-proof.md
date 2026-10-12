# Parent-supplied natural-language proof

- Parent DAG node: `root.affine_approximation-a1.density_ge_one-a1`
- Child DAG node: `root.affine_approximation-a1.density_ge_one-a1.support_lower_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 3 and 5 of the parent proof (Simon Ch. 4, 3.11 and Remark 4.10(1)). Step 3 gives the upper-semicontinuity estimate through B_t(z') contained in B_(t+eta)(y), followed by eta -> 0+. Step 5 says that the open mu-null set where the density is < 1 cannot meet spt mu. Here Step 5 is used in an equivalent form: every neighbourhood of a point of spt mu has positive measure, so it contains a point where the a.e. estimate holds. The statement is for an arbitrary measure mu.

Notation.
- B_u(z) := closedBall z u (closed) and B^o_u(z) := ball z u (open).
- M(u) := toReal(mu(B_u(y))), so M(u) >= 0.
- For x in R^(n+l), P(x) is the statement: if |x - y| < r, then omega <= (1 + c(t)) (toReal(mu(B_t(x)))/t^n) + c(t) for every t in (0, r].
- N := {x : P(x) fails}. The a.e. hypothesis says mu(N) = 0, as an outer measure; no measurability of N is needed.

Other hypotheses: omega > 0, r > 0, y in spt mu, mu(B_(2r)(y)) < infinity, c(t) >= 0 for t in (0, r], and c(t) -> 0 as t -> 0+.

1. Finite masses near y. For u <= 2r, B_u(y) is contained in B_(2r)(y). So mu(B_u(y)) <= mu(B_(2r)(y)) < infinity and mu(B_u(y)) = ofReal(M(u)).

2. Good points arbitrarily close to y. Let 0 < eta < r.
   - Since y is in spt mu, every neighbourhood of y has positive mu-measure (Measure.mem_support_iff_forall). B^o_eta(y) is such a neighbourhood, so mu(B^o_eta(y)) > 0.
   - If B^o_eta(y) were contained in N, then mu(B^o_eta(y)) <= mu(N) = 0 (measure_mono_null), a contradiction.
   - Hence there is x with |x - y| < eta and P(x). As eta < r, also |x - y| < r. So omega <= (1 + c(t)) (toReal(mu(B_t(x)))/t^n) + c(t) for every t in (0, r].

3. Comparison of balls. Fix t in (0, r] and u in (t, t + r). Put eta := u - t, so 0 < eta < r, and choose x as in step 2.
   - If |z - x| <= t, then |z - y| <= |z - x| + |x - y| < t + eta = u. So B_t(x) is contained in B_u(y).
   - Since u < 2r, step 1 gives mu(B_t(x)) <= mu(B_u(y)) < infinity. Hence toReal(mu(B_t(x))) <= M(u).
   - Because c(t) >= 0 we have 1 + c(t) > 0, and t^n > 0. So step 2 yields
     omega <= (1 + c(t)) (M(u)/t^n) + c(t) for every u in (t, t + r).

4. Letting u decrease to t.
   - The closed balls B_u(y), u > t, are Borel sets and increase with u. Their intersection over all u > t is B_t(y) (Metric.biInter_gt_closedBall). Moreover 2r > t and mu(B_(2r)(y)) < infinity.
   - By continuity of measure from above along u -> t+ (tendsto_measure_biInter_gt), mu(B_u(y)) -> mu(B_t(y)).
   - Since mu(B_t(y)) < infinity and toReal is continuous at finite points, M(u) -> M(t). Hence (1 + c(t)) (M(u)/t^n) + c(t) -> (1 + c(t)) (M(t)/t^n) + c(t) as u -> t+.
   - The inequality of step 3 holds on the right-neighbourhood (t, t + r) of t. Passing to the limit (ge_of_tendsto) gives
     (*) omega <= (1 + c(t)) (M(t)/t^n) + c(t) for every t in (0, r].

5. Case epsilon >= 1. For every s > 0, (1 - epsilon)(omega s^n) <= 0, so ofReal((1 - epsilon)(omega s^n)) = 0 <= mu(B_s(y)). Thus the inequality holds for all s > 0, in particular eventually as s -> 0+.

6. Case 0 < epsilon < 1.
   (i) Put gamma := epsilon omega / (1 + omega) > 0, so gamma (1 + omega) = epsilon omega.
   (ii) Since c(s) -> 0 as s -> 0+, there is s_0 in (0, r] such that c(s) < gamma for all s in (0, s_0).
   (iii) Fix such an s and put q := M(s)/s^n >= 0. By (*) with t = s and 0 <= c(s) < gamma,
     omega <= (1 + c(s)) q + c(s) <= (1 + gamma) q + gamma.
   (iv) Suppose q < (1 - epsilon) omega. Then (1 + gamma) q < (1 + gamma)(1 - epsilon) omega, hence
     omega < (1 + gamma)(1 - epsilon) omega + gamma
           = (1 - epsilon) omega + gamma (1 + omega) - gamma epsilon omega
           = (1 - epsilon) omega + epsilon omega - gamma epsilon omega
           = omega - gamma epsilon omega.
     This is impossible, since gamma epsilon omega > 0.
   (v) Therefore q >= (1 - epsilon) omega, i.e. M(s) = q s^n >= (1 - epsilon) omega s^n.
   (vi) As s < 2r, step 1 gives mu(B_s(y)) = ofReal(M(s)) >= ofReal((1 - epsilon)(omega s^n)), by monotonicity of ofReal.

7. Conclusion. By steps 5 and 6, for every epsilon > 0 the inequality ofReal((1 - epsilon)(omega s^n)) <= mu(B_s(y)) holds for all s in a right-neighbourhood (0, s_0) of 0, i.e. eventually along s -> 0+.

Remark (verified Lean realization; not part of the mathematical argument). The following proof was compiled with Lean v4.35.0-rc3 / Mathlib 25730c7c inside `namespace GMT.Ch05` / `namespace Submission` of GMT/Ch05/Submission.lean, before `main_theorem` (that is, in the scope of the frozen contract's `open` commands); `#print axioms` reports only propext, Classical.choice, Quot.sound, and `exact Submission.<name>` closes the comparator's generated target:

```lean
theorem aal_dge1_support_density_lower_bound : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (ω r : ℝ) (c : ℝ → ℝ), 0 < ω → 0 < r → y ∈ μ.support → μ (closedBall y (2 * r)) < ⊤ → (∀ t : ℝ, 0 < t → t ≤ r → 0 ≤ c t) → Tendsto c (𝓝[>] 0) (𝓝 0) → (∀ᵐ x ∂μ, x ∈ ball y r → ∀ t : ℝ, 0 < t → t ≤ r → ω ≤ (1 + c t) * ((μ (closedBall x t)).toReal / t ^ n) + c t) → ∀ ε : ℝ, 0 < ε → ∀ᶠ s in 𝓝[>] (0 : ℝ), ENNReal.ofReal ((1 - ε) * (ω * s ^ n)) ≤ μ (closedBall y s) := by
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

1. Masses of B_u(y) with u <= 2r are finite.
2. Since y is in spt mu, each open ball B^o_eta(y) has positive measure, so it contains a point x where the a.e. estimate holds.
3. B_t(x) is contained in B_(t+eta)(y), which transfers the estimate to omega <= (1 + c(t)) M(t+eta)/t^n + c(t).
4. Continuity of mu from above on closed balls, as eta -> 0+, gives omega <= (1 + c(t)) M(t)/t^n + c(t) for t in (0, r].
5. With gamma = epsilon omega/(1 + omega) and c(s) < gamma for small s, M(s) >= (1 - epsilon) omega s^n; the case epsilon >= 1 is trivial.

## Reference use

### local-project

Queries:
- `timeout 300 rg -n 'aal_dge1|weight_lt_top|scaledLpNorm_mono|density_le_monotone|support_density_lower' <snapshot>/project`
- `timeout 300 rg -n 'def scaledLpNorm|def weight|def support|def HasDensity|integrableOn_mult' <snapshot>/project/GMT/Ch05/Contract.lean`
- `timeout 300 rg -n 'lemma mem_support_iff_forall|theorem tendsto_measure_biInter_gt|theorem biInter_gt_closedBall|theorem withDensity_apply \(|theorem restrict_restrict \(|theorem lintegral_mono_set|theorem tendsto_toReal \{|Filter.Tendsto.rpow_const|theorem Gamma_pos_of_pos' <snapshot>/mathlib/Mathlib/{MeasureTheory/Measure/Support.lean,MeasureTheory/Measure/Continuity.lean,Topology/MetricSpace/Pseudo/Lemmas.lean,MeasureTheory/Measure/WithDensity.lean,MeasureTheory/Measure/Restrict.lean,MeasureTheory/Integral/Lebesgue/Basic.lean,Topology/Instances/ENNReal/Lemmas.lean,Analysis/SpecialFunctions/Pow/Continuity.lean,Analysis/SpecialFunctions/Gamma/Basic.lean}`
- `timeout 300 rg -n 'theorem Integrable.lintegral_lt_top|theorem measure_mono_null|theorem ae_iff' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `timeout 300 rg -n 'rpow_lt_top_iff_of_pos|theorem rpow_le_rpow \{|lemma squeeze_zero' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/Pow <snapshot>/mathlib/Mathlib/Topology/MetricSpace`
- `grep -n 'theorem scaledLpMeanCurvature_mono_ball|one_le_stationaryDensityReal_of_mem_support_lp|upperSemicontinuousOn_stationaryDensityReal_lp' .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/*.lean`
- `timeout 60 grep -rhoE '"lean_name": *"[^"]*"' --include=*.json <run-dir> | sort -u; timeout 120 grep -rl aal_dge1 <run-dir>`
- `python3 -I: verifier/gmt-compare.py contract_scope + child_modules and verifier/lean_contract.py validate_lean_statement on both child lean_statements`
- `lake build GMT.Ch05.Submission; lake env lean NodeChallenge2.lean, NodeSolution0.lean, NodeSolution1.lean (scratch projects /tmp/claude-1000/dge1-proj and /tmp/claude-1000/dge1-proj2 linked to lake-packages-25730c7c)`
- `lake env lean /tmp/claude-1000/dge1-check2/Check4.lean (contract prefix + both child proofs + assembly taking the two sibling types as explicit hypotheses; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpLowerDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-04-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-density-ge-one-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-mass-upper-bound-a1/decomposition-v1.json`
- `/tmp/claude-1000/dge1-check2/Check4.lean`
- `/tmp/claude-1000/dge1-proj2/GMT/Ch05/Submission.lean`

Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json).

No prior declarations. The rg for 'aal_dge1|weight_lt_top|scaledLpNorm_mono|density_le_monotone|support_density_lower' in <snapshot>/project has no match. No lean_name in the run's dag.json or node records uses the aal_dge1_ prefix.

Contract definitions used (project/GMT/Ch05/Contract.lean): integrableOn_mult (line 114), weight (122), support = U ∩ weight.support (127), HasDensity (157), scaledLpNorm (168).

Mathlib items located (paths under mathlib/Mathlib):
- Measure.mem_support_iff_forall (MeasureTheory/Measure/Support.lean:75): points of spt mu have neighbourhoods of positive measure.
- tendsto_measure_biInter_gt (MeasureTheory/Measure/Continuity.lean:266) and Metric.biInter_gt_closedBall (Topology/MetricSpace/Pseudo/Lemmas.lean:100): mu(B_u(y)) -> mu(B_t(y)) as u -> t+.
- measure_mono_null (MeasureTheory/OuterMeasure/Basic.lean:54) and ae_iff (MeasureTheory/OuterMeasure/AE.lean:134): a null set cannot contain a ball of positive measure.
- ENNReal.tendsto_toReal (Topology/Instances/ENNReal/Lemmas.lean:102), Filter.Tendsto.rpow_const (Analysis/SpecialFunctions/Pow/Continuity.lean:246) and squeeze_zero' (Topology/MetricSpace/Pseudo/Lemmas.lean:32): the limits in child 1.
- withDensity_apply (MeasureTheory/Measure/WithDensity.lean:44), Measure.restrict_restrict (MeasureTheory/Measure/Restrict.lean:205) and Integrable.lintegral_lt_top (MeasureTheory/Integral/IntegrableOn.lean:479): (F2) in the assembly.
- lintegral_mono_set (MeasureTheory/Integral/Lebesgue/Basic.lean:98), ENNReal.rpow_le_rpow (Analysis/SpecialFunctions/Pow/NNReal.lean:798), Real.rpow_le_rpow (Analysis/SpecialFunctions/Pow/Real.lean:549), ENNReal.rpow_lt_top_iff_of_pos (Analysis/SpecialFunctions/Pow/NNReal.lean:602) and Real.Gamma_pos_of_pos (Analysis/SpecialFunctions/Gamma/Basic.lean:443): (K-mono), (A) and omega_n > 0 in the assembly.

Pinned SimonGMT (outside the snapshot). Chapter04/LpDensity.lean:125 scaledLpMeanCurvature_mono_ball, Chapter04/LpDensity.lean:238 upperSemicontinuousOn_stationaryDensityReal_lp and Chapter04/LpLowerDensity.lean:43 one_le_stationaryDensityReal_of_mem_support_lp are the analogues of (K-mono), Step 3 and Remark 4.10(1). They are stated for the strengthened Chapter04.RectifiableVarifold, with a real-valued curvature quantity and MemLp hypotheses. The README says a bridge via Ch. 3, 1.9 would be needed, so they serve only as models and are not reused.

Lean checks:
- Both child types pass validate_lean_statement and elaborate in the comparator scope.
- The complete child proofs compile with axioms propext, Classical.choice and Quot.sound only, and exact Submission.X closes both generated targets.
- The parent assembly compiles from the two children plus the frozen types of aal_tangent_structure and aal_lp_monotonicity, taken as explicit hypotheses, with the same three axioms.
