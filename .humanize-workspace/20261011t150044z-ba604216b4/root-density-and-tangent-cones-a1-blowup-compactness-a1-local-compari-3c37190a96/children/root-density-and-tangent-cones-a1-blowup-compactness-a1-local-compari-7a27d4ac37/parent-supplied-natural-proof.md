# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.c1_tangent-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.c1_tangent-a1.lower_lipschitz-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 2 ("Lower") of the parent proof: "there is m > 0 with |g(a) − g(b)| ≥ m|a − b| for a, b ∈ B̄. Otherwise there are a_k ≠ b_k in B̄ with |g(a_k) − g(b_k)| < k⁻¹|a_k − b_k|. By compactness, pass to a subsequence with a_k → a, b_k → b, and e_k := (a_k − b_k)/|a_k − b_k| → e with |e| = 1. If a ≠ b, continuity gives g(a) = g(b), contradicting injectivity on B̄. If a = b, … |Dg(a)e| = lim_k |g(a_k) − g(b_k)|/|a_k − b_k| = 0, contradicting injectivity of Dg(a)." The parent applies this child with K = B̄ = closedBall(c, r), which is compact in ℝ^d. The only change is that B̄ is replaced by an arbitrary compact K ⊆ U. Accordingly the segment estimate of the case a = b is taken on a small ball around a inside U, where it is the mean value inequality; convexity of K is not needed.

Notation. |·| is the Euclidean norm; S := {e ∈ ℝ^d : |e| = 1}.

1. (Local facts at points of K.) Let x ∈ K. Then x ∈ U and U is open, so U is a neighbourhood of x on which g is C¹; hence g is C¹ at x (ContDiffOn.contDiffAt). In particular:
 (a) g is continuous at x;
 (b) g is strictly differentiable at x with derivative L_x := Dg(x): for every ε > 0 there is δ > 0 such that |g(y) − g(y') − L_x(y − y')| ≤ ε|y − y'| for all y, y' ∈ ball(x, δ).
 Proof of (b). Dg is continuous on the open set U because g is C¹ there. Choose δ > 0 with ball(x, δ) ⊆ U and ‖Dg(w) − L_x‖ ≤ ε for all w ∈ ball(x, δ). The map ψ(w) := g(w) − L_x w is differentiable on the convex set ball(x, δ) with ‖Dψ(w)‖ = ‖Dg(w) − L_x‖ ≤ ε. The mean value inequality gives |ψ(y) − ψ(y')| ≤ ε|y − y'| for y, y' ∈ ball(x, δ), which is the claim. (Mathlib packages (b) as ContDiffAt.hasStrictFDerivAt: HasStrictFDerivAt g (fderiv ℝ g x) x, whose isLittleO form says g(y) − g(y') − L_x(y − y') = o(|y − y'|) as (y, y') → (x, x).)

2. (Contradiction hypothesis.) Suppose no m > 0 has the stated property. Then for each k ∈ ℕ, applying this to m = 1/(k + 1) > 0, there are a_k, b_k ∈ K with
 |g(a_k) − g(b_k)| < (k + 1)⁻¹ |a_k − b_k|.   (∗)

3. (a_k ≠ b_k.) If |a_k − b_k| = 0, the right side of (∗) is 0 and (∗) would make a norm negative, which is impossible. So |a_k − b_k| > 0, and e_k := |a_k − b_k|⁻¹ (a_k − b_k) satisfies |e_k| = |a_k − b_k|⁻¹ |a_k − b_k| = 1, i.e. e_k ∈ S.

4. (Convergent subsequence.) K is compact, and S is compact (closed and bounded in the finite-dimensional space ℝ^d). So K × K × S is compact, and it contains (a_k, b_k, e_k) for every k. By sequential compactness there are (a, b, e) ∈ K × K × S and a strictly increasing φ : ℕ → ℕ with a_{φ(k)} → a, b_{φ(k)} → b and e_{φ(k)} → e. In particular a, b ∈ K and |e| = 1. Since φ(k) ≥ k, (φ(k) + 1)⁻¹ → 0.

5. (Case a ≠ b.) By 1(a) at a and at b, g(a_{φ(k)}) → g(a) and g(b_{φ(k)}) → g(b), so g(a_{φ(k)}) − g(b_{φ(k)}) → g(a) − g(b). By (∗),
 0 ≤ |g(a_{φ(k)}) − g(b_{φ(k)})| ≤ (φ(k) + 1)⁻¹ |a_{φ(k)} − b_{φ(k)}|,
 and the right side tends to 0 · |a − b| = 0. By the squeeze principle g(a_{φ(k)}) − g(b_{φ(k)}) → 0, so by uniqueness of limits g(a) − g(b) = 0. Thus g(a) = g(b) with a, b ∈ K and a ≠ b, contradicting the injectivity of g on K.

6. (Case a = b.) Put L := Dg(a); this is defined with a ∈ K. Write d_k := |a_{φ(k)} − b_{φ(k)}| > 0. Since e_{φ(k)} = d_k⁻¹(a_{φ(k)} − b_{φ(k)}) and L is linear,
 L e_{φ(k)} = d_k⁻¹ (g(a_{φ(k)}) − g(b_{φ(k)})) − d_k⁻¹ (g(a_{φ(k)}) − g(b_{φ(k)}) − L(a_{φ(k)} − b_{φ(k)})).
 Taking norms, and using (∗) on the first term,
 |L e_{φ(k)}| ≤ (φ(k) + 1)⁻¹ + |g(a_{φ(k)}) − g(b_{φ(k)}) − L(a_{φ(k)} − b_{φ(k)})| / d_k.
 The first term tends to 0 by step 4. For the second term, let ε > 0 and take δ from 1(b) at x = a. Since a_{φ(k)} → a and b_{φ(k)} → a, both points lie in ball(a, δ) for all large k, and then the quotient is ≤ ε. So the second term also tends to 0. By the squeeze principle, |L e_{φ(k)}| → 0. On the other hand L is a continuous linear map, so L e_{φ(k)} → L e and |L e_{φ(k)}| → |L e|. By uniqueness of limits |L e| = 0. Then L e = 0 = L 0, and injectivity of L = Dg(a) gives e = 0, contradicting |e| = 1.

7. (Conclusion.) Both cases are impossible, so the hypothesis of step 2 is false. Hence there is m > 0 with m|a − b| ≤ |g(a) − g(b)| for all a, b ∈ K. ∎

Implementation note (not part of the mathematics). Mathlib alone suffices; no import beyond the frozen header is needed. The appendix below is a Lean proof of exactly this type. It compiled with `lake env lean` after `import GMT.Ch07.Submission` in the comparator's replayed contract scope, with no warnings; `#print axioms` gives [propext, Classical.choice, Quot.sound]. Key names: push Not; choose; mem_sphere_zero_iff_norm; IsCompact.prod; isCompact_sphere; IsCompact.tendsto_subseq; tendsto_one_div_add_atTop_nhds_zero_nat; StrictMono.tendsto_atTop; ContDiffOn.contDiffAt; ContDiffAt.hasStrictFDerivAt (with one_ne_zero); HasStrictFDerivAt.isLittleO; Filter.Tendsto.prodMk_nhds; Asymptotics.IsLittleO.comp_tendsto; IsLittleO.norm_norm; IsLittleO.tendsto_div_nhds_zero; squeeze_zero; tendsto_nhds_unique; ContDiffAt.continuousAt.

Appendix (verified Lean draft, scope: namespace GMT.Ch07 with the contract's open commands):
```lean
theorem Submission.dtc_bc_lc_sl_c1t_lower_lipschitz : (∀ (P d : ℕ) (g : Euclid d → Euclid P) (U K : Set (Euclid d)), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 1 g U → InjOn g K → (∀ z ∈ K, Injective (fderiv ℝ g z)) → ∃ m : ℝ, 0 < m ∧ ∀ a ∈ K, ∀ b ∈ K, m * ‖a - b‖ ≤ ‖g a - g b‖) := by
  intro P d g U K hU hK hKU hg hinj hDinj
  by_contra hcon
  push Not at hcon
  -- Steps 2–3: for each `k` there are `a_k ≠ b_k` in `K` with `|g a_k - g b_k| < (k + 1)⁻¹ |a_k - b_k|`
  choose a ha b hb hab using fun k : ℕ => hcon (1 / ((k : ℝ) + 1)) (by positivity)
  have hpos : ∀ k, 0 < ‖a k - b k‖ := by
    intro k
    have h1 := hab k
    have h2 := norm_nonneg (g (a k) - g (b k))
    by_contra hle
    push Not at hle
    have h0 : ‖a k - b k‖ = 0 := le_antisymm hle (norm_nonneg _)
    rw [h0, mul_zero] at h1
    linarith
  -- Steps 3–4: unit vectors `e_k` and a convergent subsequence
  set e : ℕ → Euclid d := fun k => ‖a k - b k‖⁻¹ • (a k - b k) with he_def
  have he : ∀ k, e k ∈ sphere (0 : Euclid d) 1 := by
    intro k
    rw [mem_sphere_zero_iff_norm, he_def]
    simp only [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hpos k).ne'
  obtain ⟨⟨a0, b0, e0⟩, ⟨ha0, hb0, he0⟩, φ, hφ, hlim⟩ :=
    (hK.prod (hK.prod (isCompact_sphere (0 : Euclid d) 1))).tendsto_subseq
      (x := fun k => (a k, b k, e k)) (fun k => ⟨ha k, hb k, he k⟩)
  have hla : Tendsto (fun k => a (φ k)) atTop (𝓝 a0) := (continuous_fst.tendsto _).comp hlim
  have hlb : Tendsto (fun k => b (φ k)) atTop (𝓝 b0) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hlim
  have hle : Tendsto (fun k => e (φ k)) atTop (𝓝 e0) :=
    ((continuous_snd.comp continuous_snd).tendsto _).comp hlim
  have hinvk : Tendsto (fun k : ℕ => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop
  by_cases hab0 : a0 = b0
  · -- Step 6: `a = b`; strict differentiability of `g` at `a` forces `Dg(a) e = 0`
    subst hab0
    have hstrict : HasStrictFDerivAt g (fderiv ℝ g a0) a0 :=
      (hg.contDiffAt (hU.mem_nhds (hKU ha0))).hasStrictFDerivAt one_ne_zero
    have hpair : Tendsto (fun k => (a (φ k), b (φ k))) atTop (𝓝 (a0, a0)) := hla.prodMk_nhds hlb
    have ho := (hstrict.isLittleO.comp_tendsto hpair).norm_norm.tendsto_div_nhds_zero
    -- `|Dg(a)e_k| ≤ |g a_k - g b_k| / |a_k - b_k| + o(1) → 0`
    have hbound : ∀ k, ‖fderiv ℝ g a0 (e (φ k))‖ ≤ 1 / ((φ k : ℝ) + 1) +
        ‖g (a (φ k)) - g (b (φ k)) - fderiv ℝ g a0 (a (φ k) - b (φ k))‖ / ‖a (φ k) - b (φ k)‖ := by
      intro k
      have hk := hpos (φ k)
      have hdec : fderiv ℝ g a0 (e (φ k)) = ‖a (φ k) - b (φ k)‖⁻¹ • (g (a (φ k)) - g (b (φ k))) -
          ‖a (φ k) - b (φ k)‖⁻¹ • (g (a (φ k)) - g (b (φ k)) - fderiv ℝ g a0 (a (φ k) - b (φ k))) := by
        rw [he_def, map_smul, ← smul_sub, sub_sub_cancel]
      rw [hdec]
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hk]
        have := (hab (φ k)).le
        linarith [mul_comm (1 / ((φ k : ℝ) + 1)) ‖a (φ k) - b (φ k)‖]
      · rw [norm_smul, norm_inv, norm_norm, div_eq_inv_mul]
    have htend : Tendsto (fun k => ‖fderiv ℝ g a0 (e (φ k))‖) atTop (𝓝 0) := by
      refine squeeze_zero (fun k => norm_nonneg _) hbound ?_
      simpa using hinvk.add ho
    have hL : Tendsto (fun k => ‖fderiv ℝ g a0 (e (φ k))‖) atTop (𝓝 ‖fderiv ℝ g a0 e0‖) :=
      (((fderiv ℝ g a0).continuous.tendsto _).comp hle).norm
    have hL0 : fderiv ℝ g a0 e0 = 0 := norm_eq_zero.1 (tendsto_nhds_unique hL htend)
    have he00 : e0 = 0 := hDinj a0 ha0 (by rw [hL0, map_zero])
    rw [he00, mem_sphere_zero_iff_norm, norm_zero] at he0
    exact zero_ne_one he0
  · -- Step 5: `a ≠ b`; continuity of `g` forces `g a = g b`
    have hcont : ∀ x ∈ K, ContinuousAt g x := fun x hx =>
      (hg.contDiffAt (hU.mem_nhds (hKU hx))).continuousAt
    have hga : Tendsto (fun k => g (a (φ k))) atTop (𝓝 (g a0)) := (hcont a0 ha0).tendsto.comp hla
    have hgb : Tendsto (fun k => g (b (φ k))) atTop (𝓝 (g b0)) := (hcont b0 hb0).tendsto.comp hlb
    have hdiff : Tendsto (fun k => g (a (φ k)) - g (b (φ k))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hbd : Tendsto (fun k => 1 / ((φ k : ℝ) + 1) * ‖a (φ k) - b (φ k)‖) atTop (𝓝 0) := by
        simpa using hinvk.mul (hla.sub hlb).norm
      exact squeeze_zero (fun k => norm_nonneg _) (fun k => (hab (φ k)).le) hbd
    have hzero : g a0 - g b0 = 0 := tendsto_nhds_unique (hga.sub hgb) hdiff
    exact hab0 (hinj ha0 hb0 (sub_eq_zero.1 hzero))
```

## Key steps

1. Suppose not: for each k pick a_k, b_k ∈ K with |g(a_k) − g(b_k)| < (k+1)⁻¹|a_k − b_k|; then a_k ≠ b_k and e_k = (a_k − b_k)/|a_k − b_k| is a unit vector.
2. By compactness of K × K × S^{d−1}, a subsequence has a_{φ(k)} → a ∈ K, b_{φ(k)} → b ∈ K and e_{φ(k)} → e with |e| = 1.
3. If a ≠ b, continuity of g at a and b gives g(a) = g(b), contradicting injectivity of g on K.
4. If a = b, strict differentiability of the C¹ map g at a (mean value inequality near a) gives |Dg(a)e_{φ(k)}| ≤ (φ(k)+1)⁻¹ + o(1) → 0, so Dg(a)e = 0 with |e| = 1, contradicting injectivity of Dg(a).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD in snapshot mathlib (25730c7c759d108ef87ab70af2342a196760f79d) and project (b4d606db1da5da8fa2c0292ad4924d97de8b3c4b); simongmt rev 2b3663083f3fe399b6296fb8eaee52169170e197 in snapshot project/lake-manifest.json = workspace .lake/packages/simongmt HEAD; diff snapshot project/GMT/Ch07/Contract.lean vs workspace Contract.lean and Submission.lean (identical; Submission is a byte copy)`
- `sed -n 1,160p .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (blowUpMap, HasApproximateTangentSpaceAt = finrank ∧ Tendsto over 𝓝[>] 0 for every f : C_c)`
- `grep -n '^theorem' SimonGMT Chapter02/{WeightedArea,AreaLinearWeighted,AreaWeighted}.lean; sed WeightedArea.lean (integral_area_formula_of_injective_derivative, weighted_area_formula_volume_of_injective_derivative), AreaLinearWeighted.lean (weighted_linear_area_formula), Area.lean (areaJacobianAt), AreaApproximation.lean (continuous_normDet, measurable_areaJacobianAt)`
- `python3 -I import-closure walk from the Submission.lean imports over .lake/packages/simongmt: SimonGMT closure = Chapter01.{Basic,Hausdorff,MetricCriterion}, Chapter02.Lipschitz, Chapter03.Rectifiable (no WeightedArea / AreaLinearWeighted / AreaFormula)`
- `python3 -I tally of import headers over accepted candidate commits (892 keep the frozen header; some add Chapter02.WeightedArea, Chapter02.AreaLipschitz, BumpFunction.SmoothApprox); sed verifier/gmt-compare.py frozen_inputs/candidate_inputs (Submission.lean is excluded from the frozen byte check)`
- `python3 -I scans of dag.json (1523 nodes): lean_statement containing HasApproximateTangentSpaceAt together with ContDiff/fderiv/Lipschitz/graph; lean_name matching c1_image|lower_lipschitz; children of root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_piece_tangent-a1`
- `python3 -I /tmp/c1t_scripts/verify_reuse.py: git show <candidate_commit>:GMT/Ch07/Submission.lean, whitespace-normalised type comparison and sorry scan for codim1_rdo_c1pt_{fderiv_lower_bound,rescaled_area_formula,linear_range_integral,rescaled_integral_tendsto} and codim1_rdo_c1_piece_approxTangent (all IDENTICAL, no sorry); import-line count of commits dd15d7b, e2ca8ae, 9a707fe, 9ff7690 (8 = frozen header)`
- `lake env lean /tmp/c1t_check/reuse/Sub9ff.lean (commit 9ff76906 Submission + #print axioms)`
- `rg -n in snapshot mathlib/Mathlib: 'theorem ContDiffAt.hasStrictFDerivAt ', 'alias ⟨HasStrictFDerivAt.isLittleO', 'theorem IsCompact.tendsto_subseq ', 'theorem tendsto_one_div_add_atTop_nhds_zero_nat', 'theorem IsLittleO.tendsto_div_nhds_zero', 'theorem IsLittleO.comp_tendsto', 'theorem tendsto_integral_filter_of_dominated_convergence', 'theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero', 'theorem HasFDerivAt.lim', 'theorem ContDiffOn.continuousOn_fderiv_of_isOpen'; grep mem_sphere_zero_iff_norm, IsLittleO.norm_norm, Filter.Tendsto.prodMk_nhds`
- `grep -rl dtc_bc_lc_sl_c1t over the run directory (0 files); git log --all --oneline -S 'dtc_bc_lc_sl_c1t' over 6398 refs (0 commits)`
- `python3 -I /tmp/c1t_scripts/scope.py and /tmp/c1t_scripts/gen.py (gmt-compare.contract_scope and child_modules in contract mode; lean_contract.validate_lean_statement on all five child types)`
- `lake env lean /tmp/c1t_check/final/Challenge_{lower_lipschitz,rescaled_tendsto,fderiv_lower_bound,rescaled_area_formula,linear_range_integral}.lean, /tmp/c1t_check/assembly/Assembly.lean, /tmp/c1t_check/childA/ChildA.lean, /tmp/c1t_check/childB/ChildB.lean, /tmp/c1t_check/final/Combined.lean, /tmp/c1t_check/final/EndToEnd.lean (with #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Asymptotics/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Asymptotics/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLinearWeighted.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-3c37190a96/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-09907e06c7/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-e9bb54472d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-bab615aebf/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-272e126047/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/c1t_check/reuse/Sub9ff.lean`
- `/tmp/c1t_check/final/Challenge_lower_lipschitz.lean`
- `/tmp/c1t_check/final/Challenge_rescaled_tendsto.lean`
- `/tmp/c1t_check/final/Challenge_fderiv_lower_bound.lean`
- `/tmp/c1t_check/final/Challenge_rescaled_area_formula.lean`
- `/tmp/c1t_check/final/Challenge_linear_range_integral.lean`
- `/tmp/c1t_check/assembly/Assembly.lean`
- `/tmp/c1t_check/childA/ChildA.lean`
- `/tmp/c1t_check/childB/ChildB.lean`
- `/tmp/c1t_check/final/Combined.lean`
- `/tmp/c1t_check/final/EndToEnd.lean`

Pins match: snapshot Mathlib 25730c7c and project b4d606db; workspace SimonGMT at 2b366308. The snapshot Contract.lean equals the workspace Contract.lean, and Submission.lean is a byte copy of it.

SimonGMT has the cited weighted area formulas, in Chapter02/WeightedArea.lean and Chapter02/AreaLinearWeighted.lean, but neither is in Submission.lean's import closure.

The DAG already has comparator-accepted, sorry-free declarations whose types are verbatim the Bochner/√det forms of supplied steps 3 and 7, plus the derivative lower bound:
- codim1_rdo_c1pt_rescaled_area_formula (e2ca8ae)
- codim1_rdo_c1pt_linear_range_integral (9a707fe)
- codim1_rdo_c1pt_fderiv_lower_bound (dd15d7b)
Their commits keep the frozen header, and their axioms are [propext, Classical.choice, Quot.sound]. These three are reused.

No accepted declaration covers step 2 on a compact set, or steps 4–6 with g C¹ only on U and the closed ball:
- codim1_rdo_c1pt_rescaled_integral_tendsto needs g and the weight continuous everywhere and B open;
- codim1_rdo_c1cov_local_lower_lipschitz is only local and needs global ContDiff;
- dor_lmbsf_c1_image_approxTangent is still decomposing.
So there are two new leaves. Snapshot Mathlib supplies everything they need: ContDiffAt.hasStrictFDerivAt, IsCompact.tendsto_subseq, the isLittleO calculus, tendsto_integral_filter_of_dominated_convergence and setIntegral_eq_of_subset_of_forall_sdiff_eq_zero.

All five child types validate and elaborate in the comparator contract scope. The frozen parent type is derived from them with no sorry, and its axioms are [propext, Classical.choice, Quot.sound].
