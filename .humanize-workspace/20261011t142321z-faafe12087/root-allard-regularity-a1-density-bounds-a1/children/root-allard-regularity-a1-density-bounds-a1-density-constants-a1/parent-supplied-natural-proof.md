# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.density_bounds-a1`
- Child DAG node: `root.allard_regularity-a1.density_bounds-a1.density_constants-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof (choice of delta_P and C_P through the C^1 functions g_+, g_-, g_c and the mean value theorem), with kappa = (p-n)/(4p) and omega_n replaced by arbitrary kappa > 0 and omega > 0 and the three bounds multiplied by omega (G_+ = omega g_+, G_- = omega g_-, G_c = omega g_c). The parent applies the result with kappa = (p-n)/(4p) and omega = unitBallVolume n, before the codimension l is chosen.

Notation. Fix n, kappa > 0, omega > 0. Let I be the open interval (-1/24, 1/4); for t in I we have 1 - 3t > 1/4 > 0. For t in I put Lambda(t) := t/kappa, q(t) := (1 + t)/(1 - 3t)^n, and
 G_+(t) := e^(2 Lambda(t)) (q(t) omega) + 2 e^(Lambda(t)) Lambda(t),
 G_-(t) := e^(-Lambda(t)) (omega - Lambda(t)),
 G_c(t) := e^(Lambda(t)) (e^(Lambda(t)) (q(t) omega) + Lambda(t) - omega).

1. Smoothness. t -> Lambda(t) is linear, exp is C^infinity, t -> 1 + t is a polynomial and t -> (1 - 3t)^n is a polynomial with no zero on I, so q = (1 + t) ((1 - 3t)^n)^(-1) is C^infinity on I. Hence G_+, G_-, G_c, which are sums and products of these functions, are C^infinity (in particular C^1) on I. Explicitly, with Lambda = Lambda(t), q = q(t):
 q'(t) = (1 - 3t)^(-n) + 3n (1 + t)(1 - 3t)^(-n-1),
 G_+'(t) = (2/kappa) e^(2 Lambda) q omega + e^(2 Lambda) q'(t) omega + (2/kappa) e^Lambda (Lambda + 1),
 G_-'(t) = -(1/kappa) e^(-Lambda) (omega - Lambda + 1),
 G_c'(t) = (1/kappa) e^Lambda (e^Lambda q omega + Lambda - omega) + e^Lambda ((1/kappa) e^Lambda q omega + e^Lambda q'(t) omega + 1/kappa);
all of these are continuous on I.

2. Put t_0 := min{1/8, kappa} > 0. Then [0, t_0] is a compact interval contained in I (t_0 <= 1/8 < 1/4). By the extreme value theorem the continuous functions |G_+'|, |G_-'|, |G_c'| are bounded on [0, t_0]; fix a real A >= 0 with |G_+'(t)| <= A, |G_-'(t)| <= A and |G_c'(t)| <= A for all t in [0, t_0].

3. Values at 0. Lambda(0) = 0 and q(0) = 1, hence G_+(0) = omega, G_-(0) = omega and G_c(0) = e^0 (e^0 omega + 0 - omega) = 0.

4. Constants. Put C_P := max{1, A/omega} and delta_P := min{t_0, 1/(2 C_P)}. Then C_P >= 1 > 0 and C_P omega >= A; 0 < delta_P <= t_0 <= 1/8; delta_P <= t_0 <= kappa; and C_P delta_P <= C_P/(2 C_P) = 1/2. Only n, kappa, omega entered.

5. Inequality (a). Let 0 < t <= delta_P, so [0, t] is contained in [0, t_0]. G_+ is continuous on [0, t] and differentiable on (0, t), so the mean value theorem gives xi in (0, t) with G_+(t) - G_+(0) = G_+'(xi) t <= A t <= C_P omega t. With step 3, G_+(t) <= omega + C_P omega t = (1 + C_P t) omega. Since Lambda(t) = t/kappa and q(t) omega = (1 + t)/(1 - 3t)^n * omega, this is (a).

6. Inequality (b). Similarly there is xi' in (0, t) with G_-(t) - omega = G_-'(xi') t >= -A t >= -C_P omega t, i.e. (1 - C_P t) omega <= G_-(t) = e^(-(t/kappa)) (omega - t/kappa), which is (b).

7. Inequality (c). There is xi'' in (0, t) with G_c(t) = G_c(t) - G_c(0) = G_c'(xi'') t <= A t <= C_P omega t, i.e. e^(t/kappa) (e^(t/kappa) ((1 + t)/(1 - 3t)^n * omega) + t/kappa - omega) <= C_P omega t, which is (c).

8. Steps 4-7 give 0 < delta_P <= 1/8, delta_P <= kappa, 0 < C_P, C_P delta_P <= 1/2 and (a), (b), (c) for every t in (0, delta_P].

Appendix (non-normative implementation aid; the numbered argument above is the proof). The following Lean 4 declaration was compiled in the namespace/opens of the frozen contract (import GMT.Ch05.Submission; open MeasureTheory Metric Set Filter Topology; open scoped ENNReal NNReal; namespace GMT.Ch05; open RectifiableVarifold; namespace Submission) with Lean v4.35.0-rc3 and Mathlib 25730c7c. It adds no other declaration. #print axioms: propext, Classical.choice, Quot.sound. It follows steps 1-8: smoothness on I, a compactness bound for the derivatives on [0, t_0], the mean value inequality (Convex.norm_image_sub_le_of_norm_deriv_le), C_P = max 1 (A/omega) and delta_P = min t_0 (1/(2 C_P)).

```lean
theorem allard52_density_constants : ∀ (n : ℕ) (κ ω : ℝ), 0 < κ → 0 < ω → ∃ δP CP : ℝ, 0 < δP ∧ δP ≤ 1 / 8 ∧ δP ≤ κ ∧ 0 < CP ∧ CP * δP ≤ 1 / 2 ∧ ∀ t : ℝ, 0 < t → t ≤ δP → Real.exp (2 * (t / κ)) * ((1 + t) / (1 - 3 * t) ^ n * ω) + 2 * Real.exp (t / κ) * (t / κ) ≤ (1 + CP * t) * ω ∧ (1 - CP * t) * ω ≤ Real.exp (-(t / κ)) * (ω - t / κ) ∧ Real.exp (t / κ) * (Real.exp (t / κ) * ((1 + t) / (1 - 3 * t) ^ n * ω) + t / κ - ω) ≤ CP * ω * t := by
  intro n κ ω hκ hω
  -- Step 0: the radius `t₀ = min (1/8) κ`; `[0, t₀]` sits inside the open interval
  -- `I = (-1/24, 1/4)`, on which `1 - 3 t > 1/4 > 0`.
  obtain ⟨t₀, ht₀pos, ht₀le, ht₀κ⟩ : ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ ≤ 1 / 8 ∧ t₀ ≤ κ :=
    ⟨min (1 / 8) κ, lt_min (by norm_num) hκ, min_le_left _ _, min_le_right _ _⟩
  have hsub : Icc (0 : ℝ) t₀ ⊆ Ioo (-1 / 24 : ℝ) (1 / 4) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- Step 1: mean value inequality for a `C¹` function on `I`, on the segment `[0, t₀]`.
  have key : ∀ G : ℝ → ℝ, ContDiffOn ℝ 1 G (Ioo (-1 / 24 : ℝ) (1 / 4)) →
      ∃ A : ℝ, ∀ t ∈ Icc (0 : ℝ) t₀, |G t - G 0| ≤ A * t := by
    intro G hG
    have hcont : ContinuousOn (deriv G) (Ioo (-1 / 24 : ℝ) (1 / 4)) :=
      hG.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
    obtain ⟨A, hA⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t₀)).exists_bound_of_continuousOn
      (hcont.mono hsub)
    refine ⟨A, fun t ht => ?_⟩
    have hdiff : ∀ x ∈ Icc (0 : ℝ) t₀, DifferentiableAt ℝ G x := fun x hx =>
      (hG.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds (hsub hx))
    have h := (convex_Icc (0 : ℝ) t₀).norm_image_sub_le_of_norm_deriv_le hdiff hA
      (left_mem_Icc.2 ht₀pos.le) ht
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at h
  -- Smoothness of the three functions on `I`.
  have hden : ∀ x ∈ Ioo (-1 / 24 : ℝ) (1 / 4), (1 - 3 * x) ^ n ≠ 0 := fun x hx =>
    pow_ne_zero _ (by linarith [hx.2] : (0 : ℝ) < 1 - 3 * x).ne'
  have hR : ContDiffOn ℝ 1 (fun t : ℝ => (1 + t) / (1 - 3 * t) ^ n * ω)
      (Ioo (-1 / 24 : ℝ) (1 / 4)) := by
    apply ContDiffOn.mul _ contDiffOn_const
    exact ContDiffOn.fun_div (by fun_prop) (by fun_prop) hden
  have hE : ContDiff ℝ 1 (fun t : ℝ => Real.exp (t / κ)) := by fun_prop
  have hE2 : ContDiff ℝ 1 (fun t : ℝ => Real.exp (2 * (t / κ))) := by fun_prop
  obtain ⟨A₁, hA₁⟩ := key (fun t => Real.exp (2 * (t / κ)) * ((1 + t) / (1 - 3 * t) ^ n * ω) +
      2 * Real.exp (t / κ) * (t / κ)) ((hE2.contDiffOn.mul hR).add (by fun_prop))
  obtain ⟨A₂, hA₂⟩ := key (fun t => Real.exp (-(t / κ)) * (ω - t / κ)) (by fun_prop)
  obtain ⟨A₃, hA₃⟩ := key (fun t => Real.exp (t / κ) *
      (Real.exp (t / κ) * ((1 + t) / (1 - 3 * t) ^ n * ω) + t / κ - ω))
    (hE.contDiffOn.mul (((hE.contDiffOn.mul hR).add (by fun_prop)).sub contDiffOn_const))
  -- Step 2: the constants.
  obtain ⟨A, hA1, hA2, hA3⟩ : ∃ A : ℝ, A₁ ≤ A ∧ A₂ ≤ A ∧ A₃ ≤ A :=
    ⟨max (max A₁ A₂) A₃, le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩
  obtain ⟨CP, hCP1, hCPA⟩ : ∃ CP : ℝ, 1 ≤ CP ∧ A ≤ CP * ω :=
    ⟨max 1 (A / ω), le_max_left _ _, (div_le_iff₀ hω).1 (le_max_right _ _)⟩
  have hCPpos : 0 < CP := lt_of_lt_of_le one_pos hCP1
  refine ⟨min t₀ (1 / (2 * CP)), CP, lt_min ht₀pos (by positivity),
    le_trans (min_le_left _ _) ht₀le, le_trans (min_le_left _ _) ht₀κ, hCPpos, ?_, ?_⟩
  · calc CP * min t₀ (1 / (2 * CP)) ≤ CP * (1 / (2 * CP)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hCPpos.le
      _ = 1 / 2 := by field_simp
  · intro t ht htδ
    have htI : t ∈ Icc (0 : ℝ) t₀ := ⟨ht.le, le_trans htδ (min_le_left _ _)⟩
    have h1 := hA₁ t htI
    have h2 := hA₂ t htI
    have h3 := hA₃ t htI
    simp only [zero_div, mul_zero, neg_zero, Real.exp_zero, add_zero, sub_zero, one_pow, div_one,
      one_mul, mul_one, sub_self] at h1 h2 h3
    have hAt : A * t ≤ CP * ω * t := mul_le_mul_of_nonneg_right hCPA ht.le
    have h1' : A₁ * t ≤ A * t := mul_le_mul_of_nonneg_right hA1 ht.le
    have h2' : A₂ * t ≤ A * t := mul_le_mul_of_nonneg_right hA2 ht.le
    have h3' : A₃ * t ≤ A * t := mul_le_mul_of_nonneg_right hA3 ht.le
    refine ⟨?_, ?_, ?_⟩
    · linarith [(abs_le.1 h1).2]
    · linarith [(abs_le.1 h2).1]
    · linarith [le_abs_self (Real.exp (t / κ) *
        (Real.exp (t / κ) * ((1 + t) / (1 - 3 * t) ^ n * ω) + t / κ - ω))]
```

## Key steps

1. On I = (-1/24, 1/4) (where 1 - 3t > 1/4) define G_+ = omega g_+, G_- = omega g_-, G_c = omega g_c; they are C^1 with continuous derivatives
2. Bound |G_+'|, |G_-'|, |G_c'| by one constant A on the compact interval [0, t_0], t_0 = min{1/8, kappa}
3. G_+(0) = G_-(0) = omega and G_c(0) = 0
4. C_P := max{1, A/omega} and delta_P := min{t_0, 1/(2 C_P)} satisfy the side conditions
5. The mean value theorem on [0, t] gives (a), (b) and (c)

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean`
- `rg -c -t lean 'allard52_density_constants|allard52_annular_monotonicity|allard52_support_density_ge_one|allard52_center_density_bounds|aal_allard_subball_bounds' <snapshot>/project <snapshot>/mathlib/Mathlib`
- `for pat in Allard Varifold monotonicity_formula tangentProj; do rg -l -t lean $pat <snapshot>/mathlib/Mathlib | wc -l; done`
- `rg -n (theorem setLIntegral_iUnion_of_directed | theorem lintegral_union_le | theorem lintegral_liminf_le' | theorem tendsto_measure_biInter_gt | lemma mem_support_iff_forall | theorem LocallyIntegrableOn.integrableOn_compact_subset | theorem lintegral_lintegral_swap | theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le | theorem norm_image_sub_le_of_norm_deriv_le | theorem integral_hasDerivAt_right) MeasureTheory Analysis/Calculus/ParametricIntegral.lean Analysis/Calculus/MeanValue.lean, run in <snapshot>/mathlib/Mathlib`
- `rg -n (monoton|κ|kappa|2.4|density) <snapshot>/project/GMT/Ch05/README.md; sed -n 25,45p <snapshot>/project/GMT/Ch05/README.md`
- `grep -n (def lpMeanCurvatureKappa|structure LpAnnularCorrection|theorem HasGeneralizedMeanCurvatureIn.exists_lpAnnularCorrection) -A3 .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpAnnular.lean`
- `python3 over dag.json: lean_name, lean_statement, status, parent and candidate_commit for the five proposed names, allard52_tangent_ae, allard52_density_bounds and every accepted node`
- `git show 595bf34cad5e797b1ca2c89a3d419f3daecdab75:GMT/Ch05/Submission.lean; git show 9f4dca65df4fbd188bea65e81c59d598279e6643:GMT/Ch05/Submission.lean | grep -n 'theorem allard52_tangent_ae'; git show 4c0fc30d6a1cd4ba43b449f2e51583e4e473c461:GMT/Ch05/Submission.lean | grep -n 'theorem dohr_local_monotonicity'`
- `toolchains/lean-4.35.0-rc3-linux/bin/lean GMT/Ch05/Submission.lean -o /tmp/db3-build/lib/GMT/Ch05/Submission.olean (LEAN_PATH = /tmp/db3-build/lib plus lake-packages-25730c7c/*/.lake/build/lib/lean)`
- `LEAN_PATH=<same> lean /tmp/db3-check/Types.lean; lean /tmp/db3-check/Assembly.lean; lean /tmp/db3-check/Appx_density_constants.lean; lean /tmp/db3-check/Appx_center_density_bounds.lean; lean /tmp/db3-check/Appx_support_density_ge_one.lean; lean /tmp/db3-check/Subball.lean`
- `python3 field-by-field comparison of the proposed subproblems with nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-v2.json`
- `grep max_nodes .humanize/swarm-configs/675fa2adfe3d43c39028ca3e3199bdce.json; read _existing_lean_name_problem, _accepted_checkpoint, _install_parent_supplied_child_handoff and the node-bound check of /runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/runtime.py, and ensure in store.py`
- `sed -n 270,315p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt (Simon Ch. 5, 2.3, 2.4 and inequality (1) in the proof of 2.5)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpAnnular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/swarm-configs/675fa2adfe3d43c39028ca3e3199bdce.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/db3-check/Types.lean`
- `/tmp/db3-check/Assembly.lean`
- `/tmp/db3-check/Appx_density_constants.lean`
- `/tmp/db3-check/Appx_center_density_bounds.lean`
- `/tmp/db3-check/Appx_support_density_ge_one.lean`
- `/tmp/db3-check/Subball.lean`

Pins: project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). The workspace Contract.lean and Submission.lean are byte-identical to the snapshot copies.

Names.
- The five proposed names have no match in the snapshot project or Mathlib (rg exit status 1).
- In dag.json (200 nodes) the four new names occur nowhere.
- aal_allard_subball_bounds is the accepted node root.affine_approximation-a1.pinched_density_bounds-a1.allard_subball_bounds-a1 (candidate 595bf34c). Its frozen lean_statement is byte-identical to the proposed one, so runtime reuse is permitted.
- allard52_tangent_ae is accepted (candidate 9f4dca65, theorem at line 816) with the type used by the assembly.

Mathlib.
- The topics Allard, Varifold, monotonicity_formula and tangentProj have 0 hits, so the annular monotonicity is new.
- Lemmas used by the child proofs exist: setLIntegral_iUnion_of_directed (Lebesgue/Basic.lean:668), lintegral_union_le (Basic.lean:632), lintegral_liminf_le' (Lebesgue/Add.lean:216), tendsto_measure_biInter_gt (Measure/Continuity.lean:266), mem_support_iff_forall (Measure/Support.lean:75), LocallyIntegrableOn.integrableOn_compact_subset (LocallyIntegrable.lean:122), lintegral_lintegral_swap (Measure/Prod.lean:1071), integral_hasDerivAt_right (FundThmCalculus.lean:725), hasDerivAt_integral_of_dominated_loc_of_deriv_le (ParametricIntegral.lean:286) and norm_image_sub_le_of_norm_deriv_le (MeanValue.lean:727).

SimonGMT.
- lpMeanCurvatureKappa n p = (p - n) / (4 * p) (LpMeanCurvature.lean:76) confirms the corrected kappa.
- LpAnnularCorrection and exists_lpAnnularCorrection (LpAnnular.lean:335, 358) are proved for the library varifold with stored tangent data. The chapter README (lines 33-38) says this needs a bridge, so annular_monotonicity re-derives the result for the contract varifold.
- The accepted dohr_local_monotonicity (4c0fc30d, line 465) has the same hypotheses but no conical term and no decay rate.

Lean checks (Lean v4.35.0-rc3).
- Types.lean: every proposed type, the tangent sibling type and the frozen parent type elaborate with only sorry warnings.
- Assembly.lean proves the exact frozen parent type from the five children and allard52_tangent_ae. #print axioms lists exactly propext, Classical.choice, Quot.sound and those six declarations.
- Appendices: density_constants and center_density_bounds use standard axioms only; support_density_ge_one uses standard axioms plus aal_allard_subball_bounds and allard52_annular_monotonicity.
- The accepted subball body recompiles with standard axioms only.
- No matrix or inline-instance constructions occur; V.weight is passed directly as the abstract measure of center_density_bounds and elaborates.

Runtime. The current config has max_nodes = 1000 against 200 existing nodes, so the 4 new nodes fit. Reused accepted nodes skip handoff installation, and ensure returns existing nodes unchanged.

Source. Simon's 2.4 and the proof of 2.5 (1) confirm the pinched density and conical-integral bounds that are formalized here with explicit constants.
