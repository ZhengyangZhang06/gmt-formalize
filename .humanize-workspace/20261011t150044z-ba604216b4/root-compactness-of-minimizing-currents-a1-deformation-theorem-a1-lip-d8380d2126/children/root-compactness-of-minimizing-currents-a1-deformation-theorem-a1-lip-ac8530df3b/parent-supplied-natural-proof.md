# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1.homotopy_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof steps 1, 4 and 5. Notation: ℝ^N = Euclid N; ι(t, x) := WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) ∈ ℝ^{N+1} (the point (t, x_1, …, x_N)); Jv := ι(0, v); e₀ := EuclideanSpace.single 0 1; |α| := covectorEuclideanNorm α; D = fderiv ℝ; F^#ω(x) := (ω(F x)).compContinuousLinearMap (DF(x)); NC X means IsCompact X.support, X.mass < ∞ and boundaryMassOn X univ < ∞; C(K) := {ι(t, x) : t ∈ [0, 1], x ∈ K}; d := exteriorDerivative, on test forms exteriorDerivativeTestOn univ m (whose coercion is exteriorDerivative of the coercion, by rfl). For currents S, T on univ, (S − T)(ω) = S(ω) − T(ω) (the Sub instance of the contract), ∂T(ω) = T(dω) (GeometricCurrentOn.boundary_apply), and currents agreeing on all test forms are equal (GeometricCurrentOn.ext); limits of real sequences are unique (tendsto_nhds_unique).
1. Support of the boundary. By the third conjunct (SB) of Submission.cmcdt_lpo_current_toolkit applied to (VO), (REP): spt ∂X ⊆ spt X for every X ∈ 𝒟_{k+1}(ℝ^N).
2. Conjunct (10), setup. Fix N, N', Λ, L, F, G, H and X ∈ 𝒟_0(ℝ^N) with compact support, M(X) < ∞ and the hypothesis on H over spt X. By ext it suffices to prove, for every ω ∈ 𝒟^0(ℝ^{N'}), lpush(G, X)(ω) − lpush(F, X)(ω) = lpush(H, cyl X)(dω). Apply Submission.cmcdt_lpoh_pullback_limits to (lpush, (PA), N, N', m := 0, Λ, L, F, G, H, K := spt X, ω) (spt X is compact, F, G are Λ-Lipschitz, H is L-Lipschitz): we get β_j, ρ_{1,j}, ρ_{0,j} with its properties (i)–(v).
3. Conjunct (10), normality. boundaryMassOn X univ = 0 < ∞ (degree 0), so X is NC. By (7) for X: cyl(X) has compact support, M(cyl X) < ∞, boundaryMassOn cyl(X) univ = M(∂ cyl X) < ∞, and spt cyl(X) ⊆ C(spt X).
4. Conjunct (10), limits. By (iv) with Y := cyl(X): cyl(X)(dβ_j) → lpush(H, cyl X)(dω). By (ii) with X (spt X ⊆ K): X(ρ_{1,j}) → lpush(G, X)(ω) and X(ρ_{0,j}) → lpush(F, X)(ω). By part (a) of Submission.cmcdt_lpoh_cyl_identity (with (9), X, β_j and ρ_{1,j}, ρ_{0,j}, which satisfy the end-slice formulas by (i)): cyl(X)(dβ_j) = X(ρ_{1,j}) − X(ρ_{0,j}) for every j. Hence cyl(X)(dβ_j) → lpush(G, X)(ω) − lpush(F, X)(ω) as well, and uniqueness of limits gives lpush(G, X)(ω) − lpush(F, X)(ω) = lpush(H, cyl X)(dω) = ∂ lpush(H, cyl X)(ω). This proves (10).
5. Conjunct (11), normality. Fix the data with X ∈ 𝒟_{k+1}(ℝ^N), compact support, M(X) < ∞, M(∂X) < ∞. boundaryMassOn X univ = M(∂X) < ∞, so X is NC. ∂X is NC: spt ∂X ⊆ spt X (step 1) and spt ∂X = univ \ zeroRegion(∂X) is closed (the zero region is open), so spt ∂X is compact (IsCompact.of_isClosed_subset); M(∂X) < ∞; boundaryMassOn ∂X univ < ∞, because for k = 0 it is 0 by definition and for k = k' + 1 it is the mass of ∂∂X = 0 (GeometricCurrentOn.boundary_boundary), and the zero current has mass sSup{ofReal 0} = 0.
6. Conjunct (11), setup. By ext it suffices to show, for ω ∈ 𝒟^{k+1}(ℝ^{N'}), lpush(G, X)(ω) − lpush(F, X)(ω) − lpush(H, cyl ∂X)(ω) = lpush(H, cyl X)(dω). Apply Submission.cmcdt_lpoh_pullback_limits with m := k + 1 and K := spt X: β_j, ρ_{1,j}, ρ_{0,j} with (i)–(v). By (7) for X: cyl(X) is NC with spt cyl(X) ⊆ C(spt X). By (7) for ∂X: cyl(∂X) is NC with spt cyl(∂X) ⊆ {ι(t, x) : t ∈ [0, 1], x ∈ spt ∂X} ⊆ C(spt X) (step 1).
7. Conjunct (11), limits. (iv) with Y := cyl(X): cyl(X)(dβ_j) → lpush(H, cyl X)(dω). (iii) with Y := cyl(∂X): cyl(∂X)(β_j) → lpush(H, cyl ∂X)(ω). (ii) with X: X(ρ_{1,j}) → lpush(G, X)(ω), X(ρ_{0,j}) → lpush(F, X)(ω). Part (b) of Submission.cmcdt_lpoh_cyl_identity (X and ∂X normal by step 5, end slices by (i)): cyl(X)(dβ_j) = X(ρ_{1,j}) − X(ρ_{0,j}) − cyl(∂X)(β_j) for every j. Passing to the limit and using uniqueness of limits: lpush(H, cyl X)(dω) = lpush(G, X)(ω) − lpush(F, X)(ω) − lpush(H, cyl ∂X)(ω). Ext gives (11). □

Appendix (informative; the numbered proof above is the contract). The following tactic script was compiled with `lake env lean` after `import GMT.Ch07.Submission` (Mathlib 25730c7c) as the `by` block of the declaration `theorem Submission.cmcdt_lpoh_homotopy_formula` whose type is exactly this node's frozen lean_statement, with every cited dependency declared under its exact frozen type; it produced no errors or warnings:
  intro hVO hREP lpush cyl hPA h7 h9
  obtain ⟨hMSB, hBC, hSB, hLOC⟩ := Submission.cmcdt_lpo_current_toolkit hVO hREP
  have hID := Submission.cmcdt_lpoh_cyl_identity cyl h9
  refine ⟨?_, ?_⟩
  · intro N N' Λ L F G H X hF hG hH hXc hXm hHX
    apply GeometricCurrentOn.ext
    intro ω
    obtain ⟨β, ρ₁, ρ₀, hρ₁, hρ₀, hlimX, -, hlimY', -⟩ :=
      Submission.cmcdt_lpoh_pullback_limits lpush hPA N N' 0 Λ L F G H X.support ω hF hG hH hXc hHX
    have hXb : boundaryMassOn X univ < ∞ := by
      show (0 : ℝ≥0∞) < ∞
      exact ENNReal.zero_lt_top
    obtain ⟨hc1, hc2, hc3, hc4⟩ := h7 N 0 X hXc hXm hXb
    have h1 := hlimY' (cyl N 0 X) hc1 hc2 hc3 hc4
    obtain ⟨h2, h3⟩ := hlimX X hXc hXm hXb subset_rfl
    have heq : ∀ j, cyl N 0 X (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) 0 (β j)) =
        X (ρ₁ j) - X (ρ₀ j) :=
      fun j => hID.1 N X (β j) (ρ₁ j) (ρ₀ j) hXc hXm (hρ₁ j) (hρ₀ j)
    have h4 : Tendsto (fun j => cyl N 0 X (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) 0 (β j)))
        atTop (𝓝 (lpush N N' 0 G X ω - lpush N N' 0 F X ω)) := by
      simp_rw [heq]; exact h2.sub h3
    exact tendsto_nhds_unique h4 h1
  · intro N N' k Λ L F G H X hF hG hH hXc hXm hXbm hHX
    apply GeometricCurrentOn.ext
    intro ω
    obtain ⟨β, ρ₁, ρ₀, hρ₁, hρ₀, hlimX, hlimY, hlimY', -⟩ :=
      Submission.cmcdt_lpoh_pullback_limits lpush hPA N N' (k + 1) Λ L F G H X.support ω hF hG hH hXc hHX
    have hXb : boundaryMassOn X univ < ∞ := hXbm
    have hSBX : X.boundary.support ⊆ X.support := hSB N k X
    have hbc : IsCompact X.boundary.support :=
      hXc.of_isClosed_subset (isClosed_univ.sdiff X.boundary.isOpen_zeroRegion) hSBX
    have hbb : boundaryMassOn X.boundary univ < ∞ := by
      cases k with
      | zero =>
        show (0 : ℝ≥0∞) < ∞
        exact ENNReal.zero_lt_top
      | succ k' =>
        show X.boundary.boundary.massOn univ < ∞
        rw [GeometricCurrentOn.boundary_boundary]
        refine lt_of_le_of_lt ?_ ENNReal.zero_lt_top
        apply sSup_le
        rintro _ ⟨ω', -, rfl⟩
        simp
    obtain ⟨hc1, hc2, hc3, hc4⟩ := h7 N (k + 1) X hXc hXm hXb
    obtain ⟨hd1, hd2, hd3, hd4⟩ := h7 N k X.boundary hbc hXbm hbb
    have hd4' : (cyl N k X.boundary).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support,
        y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} := by
      intro y hy
      obtain ⟨t, ht, x, hx, rfl⟩ := hd4 hy
      exact ⟨t, ht, x, hSBX hx, rfl⟩
    have h1 := hlimY' (cyl N (k + 1) X) hc1 hc2 hc3 hc4
    have h5 := hlimY (cyl N k X.boundary) hd1 hd2 hd3 hd4'
    obtain ⟨h2, h3⟩ := hlimX X hXc hXm hXb subset_rfl
    have heq : ∀ j, cyl N (k + 1) X (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) (k + 1) (β j)) =
        X (ρ₁ j) - X (ρ₀ j) - cyl N k X.boundary (β j) :=
      fun j => hID.2 N k X (β j) (ρ₁ j) (ρ₀ j) hXc hXm hXbm hbc hbb (hρ₁ j) (hρ₀ j)
    have h4 : Tendsto (fun j => cyl N (k + 1) X
        (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) (k + 1) (β j)))
        atTop (𝓝 (lpush N N' (k + 1) G X ω - lpush N N' (k + 1) F X ω -
          lpush (N + 1) N' (k + 1) H (cyl N k X.boundary) ω)) := by
      simp_rw [heq]; exact (h2.sub h3).sub h5
    exact tendsto_nhds_unique h4 h1

## Key steps

1. (SB) of Submission.cmcdt_lpo_current_toolkit: spt ∂X ⊆ spt X; X, ∂X are NC (degree-0 convention, ∂∂X = 0, closed subset of compact).
2. For each ω, Submission.cmcdt_lpoh_pullback_limits with K = spt X gives β_j, ρ_{s,j} with the (PA) limits (ii)–(iv).
3. (7) puts cyl(X), cyl(∂X) in the scope of (iii), (iv): cyl(X)(dβ_j) → ∂lpush(H, cyl X)(ω), cyl(∂X)(β_j) → lpush(H, cyl ∂X)(ω).
4. Submission.cmcdt_lpoh_cyl_identity: cyl(X)(dβ_j) = X(ρ_{1,j}) − X(ρ_{0,j}) [− cyl(∂X)(β_j)].
5. Uniqueness of limits and GeometricCurrentOn.ext give (10) and (11).

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
