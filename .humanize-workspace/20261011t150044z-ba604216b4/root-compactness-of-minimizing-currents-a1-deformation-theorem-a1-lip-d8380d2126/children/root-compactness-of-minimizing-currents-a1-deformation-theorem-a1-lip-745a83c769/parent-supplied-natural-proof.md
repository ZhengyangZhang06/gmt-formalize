# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1.mass_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof steps 6 and 7; the empty-support case of step 6 is covered by the same argument (the hypothesis of cyl_eval_bound is then vacuous). Notation: ℝ^N = Euclid N; ι(t, x) := WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) ∈ ℝ^{N+1} (the point (t, x_1, …, x_N)); Jv := ι(0, v); e₀ := EuclideanSpace.single 0 1; |α| := covectorEuclideanNorm α; D = fderiv ℝ; F^#ω(x) := (ω(F x)).compContinuousLinearMap (DF(x)); NC X means IsCompact X.support, X.mass < ∞ and boundaryMassOn X univ < ∞; C(K) := {ι(t, x) : t ∈ [0, 1], x ∈ K}; d := exteriorDerivative, on test forms exteriorDerivativeTestOn univ m (whose coercion is exteriorDerivative of the coercion, by rfl). M(T) = T.massOn univ is the supremum of ofReal(T(ω)) over the admissible ω (tsupport ω ⊆ univ and |ω(y)| ≤ 1 for all y).
1. Setup. Fix N, N', k, Λ, L, F, G, H, X, δ with the hypotheses; X is NC and dist(F x, G x) ≤ δ for x ∈ spt X. By (7) for X, cyl(X) is NC (boundaryMassOn cyl(X) univ = M(∂ cyl X) < ∞) and spt cyl(X) ⊆ C(spt X). Write T := lpush(H, cyl X) and M := M(X) < ∞.
2. Key estimate: for every ω ∈ 𝒟^{k+1}(ℝ^{N'}) with |ω(y)| ≤ 1 for all y, |T(ω)| ≤ Λ^k·δ·M.toReal. Proof: apply Submission.cmcdt_lpoh_pullback_limits with m := k + 1, K := spt X and ω; let β_j be the resulting forms. By (iii) with Y := cyl(X): cyl(X)(β_j) → T(ω). For each j apply Submission.cmcdt_lpoh_cyl_eval_bound (with (VO), (REP), the first two conjuncts (L1), (L2) of (LB), (9), X, β_j) with a_j := δ + 2Λ/(j + 1), b := Λ ≥ 0 and c := 1: its hypothesis holds because, for x ∈ spt X and t ∈ [0, 1], (v) gives p, D with β_j(ι(t, x)) = (ω(p)).compContinuousLinearMap D, ‖De₀‖ ≤ dist(F x, G x) + 2Λ/(j + 1) ≤ a_j and ‖D(Jv)‖ ≤ Λ‖v‖, and γ := ω(p) has |γ| ≤ 1. Hence |cyl(X)(β_j)| ≤ Λ^k·a_j·1·M.toReal for all j. As j → ∞, |cyl(X)(β_j)| → |T(ω)| (continuity of |·|) and Λ^k·a_j·M.toReal → Λ^k·δ·M.toReal (2Λ/(j + 1) → 0), so le_of_tendsto_of_tendsto' gives |T(ω)| ≤ Λ^k·δ·M.toReal.
3. Mass bound. By sSup_le it suffices to show ofReal(T(ω)) ≤ ofReal δ·(2Λ)^k·M for admissible ω. Case δ ≥ 0: T(ω) ≤ |T(ω)| ≤ Λ^k·δ·M.toReal ≤ (2Λ)^k·δ·M.toReal (0 ≤ Λ ≤ 2Λ gives Λ^k ≤ (2Λ)^k, and δ·M.toReal ≥ 0); by monotonicity of ofReal, ofReal(T(ω)) ≤ ofReal(δ·(2Λ)^k·M.toReal) = ofReal δ·ofReal((2Λ)^k)·ofReal(M.toReal) = ofReal δ·(2Λ)^k·M (ENNReal.ofReal_mul for nonnegative factors, ENNReal.ofReal_pow, ofReal(2Λ) = 2·Λ in ℝ≥0∞, and ENNReal.ofReal_toReal as M ≠ ∞). Case δ < 0: Λ^k·δ·M.toReal ≤ 0, so T(ω) ≤ |T(ω)| ≤ 0 and ofReal(T(ω)) = 0 ≤ ofReal δ·(2Λ)^k·M. Taking the supremum over admissible ω gives M(lpush(H, cyl X)) ≤ ofReal δ·(2Λ)^k·M(X), which is (12). □

Appendix (informative; the numbered proof above is the contract). The following tactic script was compiled with `lake env lean` after `import GMT.Ch07.Submission` (Mathlib 25730c7c) as the `by` block of the declaration `theorem Submission.cmcdt_lpoh_mass_bound` whose type is exactly this node's frozen lean_statement, with every cited dependency declared under its exact frozen type; it produced no errors or warnings:
  intro hVO hREP hLB lpush cyl hPA h7 h9 N N' k Λ L F G H X δ hF hG hH hXc hXm hXb hHX hδ
  obtain ⟨hc1, hc2, hc3, hc4⟩ := h7 N k X hXc hXm hXb
  have key : ∀ ω : TestFormOn (univ : Set (Euclid N')) (k + 1),
      (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') (k + 1)) y) ≤ 1) →
      |lpush (N + 1) N' (k + 1) H (cyl N k X) ω| ≤ (Λ : ℝ) ^ k * δ * X.mass.toReal := by
    intro ω hω
    obtain ⟨β, -, -, -, -, -, hlimY, -, hβ⟩ :=
      Submission.cmcdt_lpoh_pullback_limits lpush hPA N N' (k + 1) Λ L F G H X.support ω hF hG hH hXc hHX
    have hlim := hlimY (cyl N k X) hc1 hc2 hc3 hc4
    have hbound : ∀ j : ℕ, |cyl N k X (β j)| ≤
        (Λ : ℝ) ^ k * (δ + 2 * (Λ : ℝ) / ((j : ℝ) + 1)) * 1 * X.mass.toReal := by
      intro j
      refine Submission.cmcdt_lpoh_cyl_eval_bound hVO hREP hLB.1 hLB.2.1 cyl h9 N N' k X (β j)
        (δ + 2 * (Λ : ℝ) / ((j : ℝ) + 1)) Λ 1 hXc hXm hXb Λ.coe_nonneg ?_
      intro x hx t ht
      obtain ⟨p, D, hpD, hDe, hDJ⟩ := hβ j x hx t ht
      exact ⟨(ω : DifferentialForm (Euclid N') (k + 1)) p, D, hpD, hω p,
        hDe.trans (by linarith [hδ x hx]), hDJ⟩
    have hl1 : Tendsto (fun j => |cyl N k X (β j)|) atTop
        (𝓝 |lpush (N + 1) N' (k + 1) H (cyl N k X) ω|) := hlim.abs
    have hsmall : Tendsto (fun j : ℕ => 2 * (Λ : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 * (Λ : ℝ))
      rw [mul_zero] at h
      refine h.congr (fun j => ?_)
      rw [mul_one_div]
    have hl2 : Tendsto (fun j : ℕ => (Λ : ℝ) ^ k * (δ + 2 * (Λ : ℝ) / ((j : ℝ) + 1)) * 1 * X.mass.toReal)
        atTop (𝓝 ((Λ : ℝ) ^ k * (δ + 0) * 1 * X.mass.toReal)) :=
      ((tendsto_const_nhds.mul (tendsto_const_nhds.add hsmall)).mul tendsto_const_nhds).mul
        tendsto_const_nhds
    have := le_of_tendsto_of_tendsto' hl1 hl2 hbound
    simpa using this
  apply sSup_le
  rintro _ ⟨ω, ⟨-, hω⟩, rfl⟩
  dsimp only
  have h := key ω hω
  have hM : X.mass ≠ ∞ := hXm.ne
  set T := lpush (N + 1) N' (k + 1) H (cyl N k X) with hT
  rcases le_or_gt 0 δ with hδ0 | hδ0
  · calc ENNReal.ofReal (T ω) ≤ ENNReal.ofReal (δ * (2 * (Λ : ℝ)) ^ k * X.mass.toReal) := by
          apply ENNReal.ofReal_le_ofReal
          have hΛ : (Λ : ℝ) ^ k ≤ (2 * (Λ : ℝ)) ^ k :=
            pow_le_pow_left₀ Λ.coe_nonneg (by linarith [Λ.coe_nonneg]) k
          calc T ω ≤ |T ω| := le_abs_self _
            _ ≤ (Λ : ℝ) ^ k * δ * X.mass.toReal := h
            _ ≤ (2 * (Λ : ℝ)) ^ k * δ * X.mass.toReal := by
                gcongr
            _ = δ * (2 * (Λ : ℝ)) ^ k * X.mass.toReal := by ring
      _ = ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hδ0, ENNReal.ofReal_toReal hM,
            ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num)]
          simp
  · have hle : T ω ≤ 0 := by
      have h0 : (Λ : ℝ) ^ k * δ * X.mass.toReal ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by positivity) hδ0.le) ENNReal.toReal_nonneg
      linarith [le_abs_self (T ω)]
    rw [ENNReal.ofReal_of_nonpos hle]
    exact bot_le

## Key steps

1. (7): cyl(X) is NC with spt cyl(X) ⊆ C(spt X).
2. For admissible ω, Submission.cmcdt_lpoh_pullback_limits gives β_j with cyl(X)(β_j) → lpush(H, cyl X)(ω) and β_j(ι(t,x)) = ω(p)∘D with ‖De₀‖ ≤ δ + 2Λ/(j+1), ‖D∘J‖ ≤ Λ.
3. Submission.cmcdt_lpoh_cyl_eval_bound: |cyl(X)(β_j)| ≤ Λ^k(δ + 2Λ/(j+1))M(X); the limit gives |lpush(H, cyl X)(ω)| ≤ Λ^k δ M(X).
4. Λ^k ≤ (2Λ)^k, ENNReal arithmetic (cases δ ≥ 0, δ < 0) and sSup over admissible ω give (12).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean workspaces/gmt-ch07/GMT/Ch07/Submission.lean (identical)`
- `git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, as in manifest.json)`
- `rg -n cmcdt_lpoh local-references/123e8435b4a2469b/project local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean' (no match)`
- `python3 scan of runs/20261011T150044Z-ba604216b4/dag.json lean_name fields (only the eight cmcdt_lpo_* siblings; no cmcdt_lpoh_* reserved), depth of the selected node (5) and ancestor depends_on lean names`
- `rg -n 'def curryLeft\b|theorem curryLeft_apply_apply|def curryLeftLI|def compContinuousLinearMap\b|theorem compContinuousLinearMap_apply|compContinuousLinearMapCLM' mathlib/Mathlib -g '*.lean'`
- `sed -n 1,200p mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `rg -n 'theorem norm_fderiv_le_of_lipschitz|theorem HasFDerivAt.smul\b|theorem Continuous.finCons|theorem IsCompact.exists_bound_of_continuousOn|theorem comp_cons|theorem norm_apply_le' mathlib/Mathlib -g '*.lean'`
- `rg -n 'EuclideanSpace.proj|EuclideanSpace.equiv' mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean; sed -n 705,725p mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean; sed -n 940,960p mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean; sed -n 975,995p mathlib/Mathlib/Topology/Constructions.lean`
- `rg -n 'theorem tendsto_one_div_add_atTop_nhds_zero_nat|theorem dist_triangle4|def compContinuousLinearMapCLM' mathlib/Mathlib -g '*.lean'`
- `cat lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean`
- `lake env lean /tmp/htpy-decomp-r5/Base.lean (#check of the API above in the frozen import closure)`
- `lake env lean /tmp/htpy-decomp-r5/Children.lean (eight child types elaborate; sorry-free assembly of the selected frozen type; #print axioms)`
- `lake env lean /tmp/htpy-decomp-r5/Glue.lean, Glue2.lean, Glue3.lean, Glue4.lean, Full.lean (child proofs from exact dependency types; Full.lean derives Submission.cmcdt_lpo_lipschitz_homotopy)`
- `python3 validate_lean_statement from /runtime/flows/gmt-claude-6c9908f72f7f/_recursive_lean/lean_contract.py on all eight lean_statements`
- `sed of /runtime/flows/gmt-claude-6c9908f72f7f/_recursive_lean/inherited.py and runtime.py (_decompose depth gate, _dependency_problem, _existing_lean_name_problem)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-d8380d2126/parent-child-handoff.json`
- `/tmp/htpy-decomp-r5/Children.lean`
- `/tmp/htpy-decomp-r5/Full.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same Ch07 contract as the workspace Submission.lean. It contains no cmcdt_lpoh_* declaration and no reusable proof of the homotopy statement. The Lean API the child proofs use is in the frozen import closure: ContinuousAlternatingMap.curryLeft, curryLeft_apply_apply, curryLeftLI, curryLeft_compContinuousLinearMap, compContinuousLinearMap_apply, compContinuousLinearMapCLM, EuclideanSpace.proj, PiLp.norm_apply_le, EuclideanSpace.norm_eq, norm_fderiv_le_of_lipschitz, HasFDerivAt.smul, Continuous.finCons, Fin.comp_cons, IsCompact.exists_bound_of_continuousOn, tendsto_one_div_add_atTop_nhds_zero_nat, dist_triangle4, tendsto_nhds_unique, le_of_tendsto_of_tendsto' and ContinuousLinearMap.opNorm_le_bound. ContinuousLinearMap.add_apply, smul_apply, sub_apply and coe_comp' are deprecated here; the generic add_apply, smul_apply, sub_apply and ContinuousLinearMap.coe_comp are used instead. From SimonGMT Chapter 6 they use GeometricCurrentOn.ext, boundary_apply, boundary_boundary, exteriorDerivativeTestOn, support = univ \ zeroRegion with isOpen_zeroRegion, and massOn as a supremum over massAdmissibleOn. All eight child types elaborate. With the four inherited sibling theorems declared under their exact frozen types, the eight child proofs and the parent assembly of the exact selected frozen type compile without errors or warnings; interp_calculus and phi_bound are axiom-clean.
