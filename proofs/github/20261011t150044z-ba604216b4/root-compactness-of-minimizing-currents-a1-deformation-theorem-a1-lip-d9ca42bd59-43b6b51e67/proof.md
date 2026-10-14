# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1.cyl_eval_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 7 (cyl(X)(β_j) = X(θ_j), the pointwise bound on f_j(t) = Φ(β_j(ι(t, x))), the Minkowski bound (slice (e)) and (MSB)), for an arbitrary test form β of the stated pulled-back shape. Notation: ℝ^N = Euclid N; ι(t, x) := WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) ∈ ℝ^{N+1} (the point (t, x_1, …, x_N)); Jv := ι(0, v); e₀ := EuclideanSpace.single 0 1; |α| := covectorEuclideanNorm α; D = fderiv ℝ; F^#ω(x) := (ω(F x)).compContinuousLinearMap (DF(x)); NC X means IsCompact X.support, X.mass < ∞ and boundaryMassOn X univ < ∞; C(K) := {ι(t, x) : t ∈ [0, 1], x ∈ K}; d := exteriorDerivative, on test forms exteriorDerivativeTestOn univ m (whose coercion is exteriorDerivative of the coercion, by rfl).
1. Slice. Apply (9) to X and β: there is θ ∈ 𝒟^k(ℝ^N) with θ(x)(v) = ∫_0^1 β(ι(t, x))(Fin.cons e₀ (J ∘ v)) dt for all x, v, and cyl(X)(β) = X(θ).
2. Reduction. The first conjunct (MSB) of Submission.cmcdt_lpo_current_toolkit (applied to (VO), (REP)) says: if M(X) < ∞ and |θ(x)| ≤ c' for every x ∈ spt X, then |X(θ)| ≤ c'·M(X). We apply it with c' := b^k·a·c, so it remains to show |θ(x)| ≤ b^k·a·c for every x ∈ spt X (if spt X = ∅ there is nothing to show). Then |cyl(X)(β)| = |X(θ)| ≤ b^k·a·c·M(X).
3. The integrand. Fix x ∈ spt X. Let J be the continuous linear map v ↦ ι(0, v) (as in Submission.cmcdt_lpoh_phi_bound, step 1) and f(t) := ((β(ι(t, x))).curryLeft e₀).compContinuousLinearMap J, a k-covector on ℝ^N. Then f(t)(v) = β(ι(t, x))(Fin.cons e₀ (J ∘ v)) (curryLeft_apply_apply), hence θ(x)(v) = ∫_0^1 f(t)(v) dt for all v. f is continuous: t ↦ ι(t, x) is continuous, β is continuous (it is smooth), γ ↦ γ.curryLeft is the linear isometry ContinuousAlternatingMap.curryLeftLI, evaluation at e₀ is continuous linear (ContinuousLinearMap.apply), and γ' ↦ γ'.compContinuousLinearMap J is the continuous linear map ContinuousAlternatingMap.compContinuousLinearMapCLM J.
4. Pointwise bound. Let t ∈ [0, 1] and take γ, D from the hypothesis (at x, t). Then f(t)(v) = (γ.compContinuousLinearMap D)(Fin.cons e₀ (J ∘ v)) for all v, so Submission.cmcdt_lpoh_phi_bound (with (L1), (L2), φ := f(t), a, b) gives |f(t)| ≤ b^k·a·|γ|. Since a ≥ ‖De₀‖ ≥ 0 and b^k ≥ 0, b^k·a ≥ 0, and |γ| ≤ c gives |f(t)| ≤ b^k·a·c.
5. Minkowski bound. Conjunct (e) of Submission.cmcdt_lpo_slice_forms, applied to α := θ(x), the continuous f of step 3 and the constant b^k·a·c (step 4 gives the bound for all t ∈ [0, 1]), yields |θ(x)| ≤ b^k·a·c. With step 2 this proves |cyl(X)(β)| ≤ b^k·a·c·M(X). □

Appendix (informative; the numbered proof above is the contract). The following tactic script was compiled with `lake env lean` after `import GMT.Ch07.Submission` (Mathlib 25730c7c) as the `by` block of the declaration `theorem Submission.cmcdt_lpoh_cyl_eval_bound` whose type is exactly this node's frozen lean_statement, with every cited dependency declared under its exact frozen type; it produced no errors or warnings:
  intro hVO hREP hL1 hL2 cyl h9 N N' k X β a b c hXc hXm hXb hb hβ
  obtain ⟨hMSB, -, -, -⟩ := Submission.cmcdt_lpo_current_toolkit hVO hREP
  obtain ⟨-, -, -, -, he⟩ := Submission.cmcdt_lpo_slice_forms
  obtain ⟨θ, hθ, hcyl⟩ := h9 N k X hXc hXm hXb β
  rw [hcyl]
  apply hMSB N k X θ (b ^ k * a * c) hXm
  intro x hx
  let Jl : Euclid N →ₗ[ℝ] Euclid (N + 1) :=
    { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
      map_add' := by
        intro v w
        ext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp
      map_smul' := by
        intro r v
        ext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp }
  let Jc : Euclid N →L[ℝ] Euclid (N + 1) := LinearMap.toContinuousLinearMap Jl
  have hJc : ∀ v, Jc v = WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)) := fun v => rfl
  let f : ℝ → Covector (Euclid N) k := fun t =>
    (((β : DifferentialForm (Euclid (N + 1)) (k + 1))
      (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))).curryLeft (EuclideanSpace.single 0 1)).compContinuousLinearMap Jc
  have hβc : Continuous (β : DifferentialForm (Euclid (N + 1)) (k + 1)) :=
    β.property.1.1.continuous
  have hιc : Continuous (fun t : ℝ => (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1))) := by
    fun_prop
  have hf : Continuous f := by
    have h1 : Continuous (fun t : ℝ => (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ)
        (E := Euclid (N + 1)) (F := ℝ) (n := k))
        ((β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))))) :=
      (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Euclid (N + 1)) (F := ℝ) (n := k)).continuous.comp
        (hβc.comp hιc)
    have h2 := (ContinuousAlternatingMap.compContinuousLinearMapCLM Jc).continuous.comp
      ((ContinuousLinearMap.apply ℝ _ (EuclideanSpace.single 0 1 : Euclid (N + 1))).continuous.comp h1)
    exact h2
  have hfv : ∀ (t : ℝ) (v : Fin k → Euclid N), f t v =
      (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))
        (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) := by
    intro t v
    rfl
  apply he N k ((θ : DifferentialForm (Euclid N) k) x) f (b ^ k * a * c) hf
  · intro v
    rw [hθ x v]
    simp only [hfv]
  · intro t ht
    obtain ⟨γ, D, hβeq, hγ, hDe, hDJ⟩ := hβ x hx t ht
    have hphi := Submission.cmcdt_lpoh_phi_bound hL1 hL2 N N' k γ D (f t) a b hb hDe hDJ
      (by intro v; rw [hfv, hβeq])
    have ha : 0 ≤ a := (norm_nonneg _).trans hDe
    calc covectorEuclideanNorm (f t) ≤ b ^ k * a * covectorEuclideanNorm γ := hphi
      _ ≤ b ^ k * a * c := by
        apply mul_le_mul_of_nonneg_left hγ
        exact mul_nonneg (pow_nonneg hb k) ha

## Key steps

1. (9) gives θ with cyl(X)(β) = X(θ) and θ(x)(v) = ∫_0^1 β(ι(t,x))(e₀, Jv) dt.
2. By (MSB) of Submission.cmcdt_lpo_current_toolkit it suffices to bound |θ(x)| ≤ b^k a c on spt X.
3. f(t) := (β(ι(t,x)).curryLeft e₀).compContinuousLinearMap J is continuous with θ(x)(v) = ∫ f(t)(v) dt.
4. Submission.cmcdt_lpoh_phi_bound gives |f(t)| ≤ b^k a |γ| ≤ b^k a c; slice (e) of Submission.cmcdt_lpo_slice_forms gives |θ(x)| ≤ b^k a c.

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
