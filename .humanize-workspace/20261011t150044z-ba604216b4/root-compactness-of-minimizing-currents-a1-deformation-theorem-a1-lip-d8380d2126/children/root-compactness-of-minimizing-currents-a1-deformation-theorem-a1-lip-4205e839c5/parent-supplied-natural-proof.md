# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1.interp_calculus-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 2(a), 2(b) (the interpolation H_j(y) := F_j(tail y) + y_0·(G_j(tail y) − F_j(tail y)) and its derivative), carried out for arbitrary C^∞ maps f, g. Notation: ℝ^N = Euclid N; ι(t, x) := WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) ∈ ℝ^{N+1} (the point (t, x_1, …, x_N)); Jv := ι(0, v); e₀ := EuclideanSpace.single 0 1; |α| := covectorEuclideanNorm α; D = fderiv ℝ; F^#ω(x) := (ω(F x)).compContinuousLinearMap (DF(x)); NC X means IsCompact X.support, X.mass < ∞ and boundaryMassOn X univ < ∞; C(K) := {ι(t, x) : t ∈ [0, 1], x ∈ K}; d := exteriorDerivative, on test forms exteriorDerivativeTestOn univ m (whose coercion is exteriorDerivative of the coercion, by rfl).
1. Coordinate maps. Let tl : ℝ^{N+1} → ℝ^N, tl(y) := WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) (delete coordinate 0), and hd : ℝ^{N+1} → ℝ, hd(y) := y_0 (EuclideanSpace.proj 0). tl is additive and homogeneous (both identities hold coordinatewise, by rfl), so it is a linear map and, the spaces being finite dimensional, a continuous linear map (LinearMap.toContinuousLinearMap); hd is continuous linear (EuclideanSpace.proj).
2. Values. Since Fin.tail (Fin.cons t p) = p and (Fin.cons t p) 0 = t, we get tl(ι(t, x)) = x and hd(ι(t, x)) = t for all t, x; in particular tl(Jv) = v and hd(Jv) = 0. All coordinates i.succ of e₀ = EuclideanSpace.single 0 1 vanish and its coordinate 0 is 1, so tl(e₀) = 0 and hd(e₀) = 1.
3. Norms. For w ∈ ℝ^{N+1}, ‖w‖² = |w_0|² + Σ_{i<N} |w_{i+1}|² and ‖tl w‖² = Σ_{i<N} |w_{i+1}|² (EuclideanSpace.norm_eq, Fin.sum_univ_succ), hence ‖tl w‖ ≤ ‖w‖ (Real.sqrt_le_sqrt); and |hd w| = |w_0| ≤ ‖w‖ (PiLp.norm_apply_le).
4. Definition. Put h(y) := f(tl y) + hd(y)·(g(tl y) − f(tl y)). Continuous linear maps are C^∞ and f, g are C^∞, so h is C^∞ (ContDiff.comp, ContDiff.sub, ContDiff.smul, ContDiff.add).
5. Claim (a). By step 2, h(ι(t, x)) = f(x) + t·(g(x) − f(x)).
6. Derivative. f and g are differentiable (C^∞). By the chain rule, f∘tl has derivative Df(tl y)∘tl at y, and g∘tl has derivative Dg(tl y)∘tl. By the product rule for a scalar function times a vector-valued function (HasFDerivAt.smul with c := hd, whose derivative is hd itself), y ↦ hd(y)·(g(tl y) − f(tl y)) has derivative hd(y)·(Dg(tl y)∘tl − Df(tl y)∘tl) + hd.smulRight(g(tl y) − f(tl y)). Adding (HasFDerivAt.add) and using HasFDerivAt.fderiv: for all y, w ∈ ℝ^{N+1}, Dh(y)w = Df(tl y)(tl w) + hd(y)·(Dg(tl y)(tl w) − Df(tl y)(tl w)) + hd(w)·(g(tl y) − f(tl y)).
7. Claim (b). Take y = ι(t, x) and w = e₀. By step 2, tl y = x, hd y = t, tl e₀ = 0 and hd e₀ = 1, so by step 6 Dh(y)e₀ = Df(x)0 + t·(Dg(x)0 − Df(x)0) + 1·(g(x) − f(x)) = g(x) − f(x).
8. Claim (c). Take y = ι(t, x) and w = Jv. Then tl w = v and hd w = 0, so Dh(y)(Jv) = Df(x)v + t·(Dg(x)v − Df(x)v) + 0·(…) = Df(x)v + t(Dg(x)v − Df(x)v).
9. Claim (d). Let y = ι(t, x) and w ∈ ℝ^{N+1}. By step 6 (with tl y = x, hd y = t), the triangle inequality, ‖Au‖ ≤ ‖A‖‖u‖ and step 3: ‖Dh(y)w‖ ≤ ‖Df(x)‖‖tl w‖ + |t|(‖Dg(x)‖‖tl w‖ + ‖Df(x)‖‖tl w‖) + |hd w|·‖g(x) − f(x)‖ ≤ (‖g(x) − f(x)‖ + ‖Df(x)‖ + |t|(‖Dg(x)‖ + ‖Df(x)‖))·‖w‖. The constant in parentheses is ≥ 0, so ContinuousLinearMap.opNorm_le_bound gives (d). □

Appendix (informative; the numbered proof above is the contract). The following tactic script was compiled with `lake env lean` after `import GMT.Ch07.Submission` (Mathlib 25730c7c) as the `by` block of the declaration `theorem Submission.cmcdt_lpoh_interp_calculus` whose type is exactly this node's frozen lean_statement, with every cited dependency declared under its exact frozen type; it produced no errors or warnings:
  intro N N' f g hf hg
  let tlL : Euclid (N + 1) →ₗ[ℝ] Euclid N :=
    { toFun := fun y => WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))
      map_add' := by intro y z; rfl
      map_smul' := by intro r y; rfl }
  let tl : Euclid (N + 1) →L[ℝ] Euclid N := LinearMap.toContinuousLinearMap tlL
  let hd : Euclid (N + 1) →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin (N + 1))
  have htl : ∀ y, tl y = WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) := fun y => rfl
  have hhd : ∀ y : Euclid (N + 1), hd y = WithLp.ofLp y 0 := fun y => rfl
  have htlι : ∀ (t : ℝ) (x : Euclid N), tl (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = x := by
    intro t x; rw [htl]; simp
  have hhdι : ∀ (t : ℝ) (x : Euclid N), hd (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = t := by
    intro t x; rw [hhd]; simp
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  set h : Euclid (N + 1) → Euclid N' := fun y => f (tl y) + hd y • (g (tl y) - f (tl y)) with hh
  have hderiv : ∀ y, HasFDerivAt h ((fderiv ℝ f (tl y)).comp tl +
      (hd y • ((fderiv ℝ g (tl y)).comp tl - (fderiv ℝ f (tl y)).comp tl) +
        hd.smulRight (g (tl y) - f (tl y)))) y := by
    intro y
    have h1 : HasFDerivAt (fun y => f (tl y)) ((fderiv ℝ f (tl y)).comp tl) y :=
      (hfd (tl y)).hasFDerivAt.comp y tl.hasFDerivAt
    have h2 : HasFDerivAt (fun y => g (tl y)) ((fderiv ℝ g (tl y)).comp tl) y :=
      (hgd (tl y)).hasFDerivAt.comp y tl.hasFDerivAt
    exact h1.add (hd.hasFDerivAt.smul (h2.sub h1))
  have hfd' : ∀ y, fderiv ℝ h y = (fderiv ℝ f (tl y)).comp tl +
      (hd y • ((fderiv ℝ g (tl y)).comp tl - (fderiv ℝ f (tl y)).comp tl) +
        hd.smulRight (g (tl y) - f (tl y))) := fun y => (hderiv y).fderiv
  have htle : tl (EuclideanSpace.single 0 1) = 0 := by
    rw [htl]; ext i; simp [Fin.tail]
  have hhde : hd (EuclideanSpace.single 0 1 : Euclid (N + 1)) = 1 := by
    rw [hhd]; simp
  have htlJ : ∀ v : Euclid N, tl (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = v := fun v => htlι 0 v
  have hhdJ : ∀ v : Euclid N, hd (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = 0 := fun v => hhdι 0 v
  have htln : ∀ w : Euclid (N + 1), ‖tl w‖ ≤ ‖w‖ := by
    intro w
    rw [htl, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    rw [Fin.sum_univ_succ]
    simp only [Fin.tail]
    have : 0 ≤ ‖WithLp.ofLp w 0‖ ^ 2 := by positivity
    linarith
  have hhdn : ∀ w : Euclid (N + 1), |hd w| ≤ ‖w‖ := by
    intro w
    rw [hhd, ← Real.norm_eq_abs]
    exact PiLp.norm_apply_le w 0
  refine ⟨h, (hf.comp tl.contDiff).add (hd.contDiff.smul ((hg.comp tl.contDiff).sub (hf.comp tl.contDiff))),
    ?_, ?_, ?_, ?_⟩
  · intro t x
    simp only [hh, htlι, hhdι]
  · intro t x
    rw [hfd']
    simp only [_root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      _root_.smul_apply, _root_.sub_apply,
      ContinuousLinearMap.smulRight_apply, htle, hhde, map_zero, sub_self, smul_zero, zero_add, one_smul,
      htlι]
  · intro t x v
    rw [hfd']
    simp only [_root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      _root_.smul_apply, _root_.sub_apply,
      ContinuousLinearMap.smulRight_apply, htlJ, hhdJ, zero_smul, add_zero, htlι, hhdι]
  · intro t x
    rw [hfd']
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    simp only [_root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      _root_.smul_apply, _root_.sub_apply,
      ContinuousLinearMap.smulRight_apply, htlι, hhdι]
    have e1 : ‖fderiv ℝ f x (tl w)‖ ≤ ‖fderiv ℝ f x‖ * ‖w‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact htln w)
    have e2 : ‖fderiv ℝ g x (tl w)‖ ≤ ‖fderiv ℝ g x‖ * ‖w‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact htln w)
    have e3 : ‖hd w • (g x - f x)‖ ≤ ‖g x - f x‖ * ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs, mul_comm]
      gcongr
      exact hhdn w
    calc ‖fderiv ℝ f x (tl w) + (t • (fderiv ℝ g x (tl w) - fderiv ℝ f x (tl w)) + hd w • (g x - f x))‖
        ≤ ‖fderiv ℝ f x (tl w)‖ + (‖t • (fderiv ℝ g x (tl w) - fderiv ℝ f x (tl w))‖ + ‖hd w • (g x - f x)‖) :=
          (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ ‖fderiv ℝ f x‖ * ‖w‖ + (|t| * (‖fderiv ℝ g x‖ * ‖w‖ + ‖fderiv ℝ f x‖ * ‖w‖) + ‖g x - f x‖ * ‖w‖) := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs]
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add e2 e1)
      _ = (‖g x - f x‖ + ‖fderiv ℝ f x‖ + |t| * (‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖)) * ‖w‖ := by ring

## Key steps

1. tl (delete coordinate 0) and hd (coordinate 0) are continuous linear with tl∘ι(t,·) = id, hd∘ι(t,·) ≡ t, tl e₀ = 0, hd e₀ = 1, tl∘J = id, hd∘J = 0, ‖tl w‖ ≤ ‖w‖, |hd w| ≤ ‖w‖.
2. h := f∘tl + hd·(g∘tl − f∘tl) is C^∞ and h(ι(t,x)) = f(x) + t(g(x) − f(x)).
3. Chain and product rules: Dh(y)w = Df(tl y)(tl w) + hd(y)(Dg(tl y) − Df(tl y))(tl w) + hd(w)(g(tl y) − f(tl y)).
4. Evaluate at w = e₀ and w = Jv for (b), (c); bound the three terms and apply opNorm_le_bound for (d).

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
