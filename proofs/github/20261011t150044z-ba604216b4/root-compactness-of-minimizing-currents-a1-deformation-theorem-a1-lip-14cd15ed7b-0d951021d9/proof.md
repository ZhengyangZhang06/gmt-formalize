# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1.pullback_limits-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 3 (cut-off pull-backs β_j = H_j^#ω near C, end slices ρ_{s,j}, and (PA) applied to G, F and H), together with the pointwise description of β_j used in parent step 7. Notation: ℝ^N = Euclid N; ι(t, x) := WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) ∈ ℝ^{N+1} (the point (t, x_1, …, x_N)); Jv := ι(0, v); e₀ := EuclideanSpace.single 0 1; |α| := covectorEuclideanNorm α; D = fderiv ℝ; F^#ω(x) := (ω(F x)).compContinuousLinearMap (DF(x)); NC X means IsCompact X.support, X.mass < ∞ and boundaryMassOn X univ < ∞; C(K) := {ι(t, x) : t ∈ [0, 1], x ∈ K}; d := exteriorDerivative, on test forms exteriorDerivativeTestOn univ m (whose coercion is exteriorDerivative of the coercion, by rfl).
1. Approximations. Apply Submission.cmcdt_lpoh_smooth_approx to (N, N', Λ, F, G, H, K): we obtain C^∞ maps F_j, G_j, H_j and Λ' ∈ ℝ with its properties (1)–(9).
2. Compactness of C := C(K). C is the image of the compact set [0, 1] × K under the continuous map (t, x) ↦ ι(t, x) (PiLp.continuous_toLp, Continuous.finCons, PiLp.continuous_ofLp), hence compact. For every s ∈ ℝ, x ↦ ι(s, x) is continuous.
3. Cut-off pull-backs. For each j apply Submission.cmcdt_lpo_cutoff_pullback (the sibling (CP)) to (N + 1, N', m, H_j, ω, C) (H_j is C^∞, C is compact): there are β_j ∈ 𝒟^m(ℝ^{N+1}) and an open W_j ⊇ C with β_j(y) = (ω(H_j y)).compContinuousLinearMap (DH_j(y)) and dβ_j(y) = (dω(H_j y)).compContinuousLinearMap (DH_j(y)) for every y ∈ W_j (choose these for all j).
4. End slices. For s ∈ ℝ and each j, conjunct (b) of Submission.cmcdt_lpo_slice_forms applied to (N, m, s, β_j) gives ρ_{s,j} ∈ 𝒟^m(ℝ^N) with ρ_{s,j}(x)(v) = β_j(ι(s, x))(Jv_1, …, Jv_m) for all x, v. Taking s = 1 and s = 0 gives (i).
5. Claim (ii). Let X be NC with spt X ⊆ K, and fix s ∈ {1, 0}; write (E, E_j) := (G, G_j) if s = 1 and (F, F_j) if s = 0. By smooth_approx (4), (5): H_j(ι(s, x)) = E_j(x) and DH_j(ι(s, x))(Jv) = DE_j(x)v. Let V_j := {x : ι(s, x) ∈ W_j}; it is open (step 2), and spt X ⊆ K ⊆ V_j because ι(s, x) ∈ C ⊆ W_j for x ∈ K (s ∈ [0, 1]). For x ∈ V_j and v: ρ_{s,j}(x)(v) = β_j(ι(s, x))(Jv_1, …) = ω(H_j(ι(s, x)))(DH_j(ι(s, x))(Jv_1), …) = ω(E_j x)(DE_j(x)v_1, …) = E_j^#ω(x)(v); so ρ_{s,j}(x) = E_j^#ω(x) on V_j (ContinuousAlternatingMap.ext). Now apply (PA) with (N, N', m, Λ, Λ' := Λ, E, E_j, X, ω, ρ_{s,j}): E is Λ-Lipschitz; X is NC; E_j is C^∞; ‖DE_j(x)‖ ≤ Λ for all x (smooth_approx (2)); E_j → E uniformly on ℝ^N, hence on spt X (smooth_approx (3)); and each ρ_{s,j} equals E_j^#ω on the open V_j ⊇ spt X. Hence X(ρ_{s,j}) → lpush(E, X)(ω), which is (ii).
6. Claim (iii). Let Y ∈ 𝒟_m(ℝ^{N+1}) be NC with spt Y ⊆ C. Apply (PA) with (N + 1, N', m, L, Λ', H, H_j, Y, ω, β_j): H is L-Lipschitz; Y is NC; H_j is C^∞; for y ∈ spt Y ⊆ C write y = ι(t, x) with t ∈ [0, 1], x ∈ K, so ‖DH_j(y)‖ ≤ Λ' (smooth_approx (8)); H_j → H uniformly on C ⊇ spt Y (smooth_approx (9), TendstoUniformlyOn.mono); β_j = H_j^#ω on W_j ⊇ C ⊇ spt Y (step 3). Hence Y(β_j) → lpush(H, Y)(ω).
7. Claim (iv). Same as step 6 in degree m + 1 with the form dω = exteriorDerivativeTestOn univ m ω ∈ 𝒟^{m+1}(ℝ^{N'}) and the sequence dβ_j = exteriorDerivativeTestOn univ m β_j: the coercions of these test forms are exteriorDerivative ω and exteriorDerivative β_j, and step 3 gives dβ_j = H_j^#(dω) on W_j ⊇ spt Y. Hence Y(dβ_j) → lpush(H, Y)(dω).
8. Claim (v). For x ∈ K and t ∈ [0, 1], ι(t, x) ∈ C ⊆ W_j, so by step 3 β_j(ι(t, x)) = (ω(p)).compContinuousLinearMap D with p := H_j(ι(t, x)) and D := DH_j(ι(t, x)). The two bounds are smooth_approx (6) and (7). □

Appendix (informative; the numbered proof above is the contract). The following tactic script was compiled with `lake env lean` after `import GMT.Ch07.Submission` (Mathlib 25730c7c) as the `by` block of the declaration `theorem Submission.cmcdt_lpoh_pullback_limits` whose type is exactly this node's frozen lean_statement, with every cited dependency declared under its exact frozen type; it produced no errors or warnings:
  intro lpush hPA N N' m Λ L F G H K ω hF hG hH hK hHK
  obtain ⟨Fs, Gs, Hs, Λ', hFs, hGs, hHs, hDF, hDG, hFu, hGu, hH1, hH0, hDH1, hDH0, hDe, hDJ, hDHb,
    hHu⟩ := Submission.cmcdt_lpoh_smooth_approx N N' Λ F G H K hF hG hK hHK
  set C : Set (Euclid (N + 1)) := {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K,
    y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} with hC
  have hιc : ∀ s : ℝ, Continuous
      (fun x : Euclid N => (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) : Euclid (N + 1))) := by
    intro s
    exact (PiLp.continuous_toLp 2 _).comp (continuous_const.finCons (PiLp.continuous_ofLp 2 _))
  have hCc : IsCompact C := by
    have : C = (fun p : ℝ × Euclid N =>
        (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) '' (Icc (0 : ℝ) 1 ×ˢ K) := by
      ext y; constructor
      · rintro ⟨t, ht, x, hx, rfl⟩; exact ⟨(t, x), ⟨ht, hx⟩, rfl⟩
      · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩; exact ⟨t, ht, x, hx, rfl⟩
    rw [this]
    exact (isCompact_Icc.prod hK).image (by fun_prop)
  have hCP := fun j => Submission.cmcdt_lpo_cutoff_pullback (N + 1) N' m (Hs j) ω C (hHs j) hCc
  choose β W hWo hCW hβW hdβW using hCP
  have hslice := (Submission.cmcdt_lpo_slice_forms).2.1
  choose ρ hρ using fun (s : ℝ) (j : ℕ) => hslice N m s (β j)
  refine ⟨β, ρ 1, ρ 0, fun j x v => hρ 1 j x v, fun j x v => hρ 0 j x v, ?_, ?_, ?_, ?_⟩
  · intro X hXc hXm hXb hXK
    have hend : ∀ (s : ℝ) (Es : ℕ → Euclid N → Euclid N'),
        (∀ (j : ℕ) (x : Euclid N), Hs j (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) = Es j x) →
        (∀ (j : ℕ) (x v : Euclid N), fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
          (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ (Es j) x v) →
        s ∈ Icc (0 : ℝ) 1 → ∀ j, ∃ W' : Set (Euclid N), IsOpen W' ∧ X.support ⊆ W' ∧ ∀ x ∈ W',
          (ρ s j : DifferentialForm (Euclid N) m) x =
            ((ω : DifferentialForm (Euclid N') m) (Es j x)).compContinuousLinearMap
              (fderiv ℝ (Es j) x) := by
      intro s Es hE hDE hs j
      refine ⟨(fun x : Euclid N => (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) : Euclid (N + 1))) ⁻¹' W j,
        (hWo j).preimage (hιc s), fun x hx => hCW j ⟨s, hs, x, hXK hx, rfl⟩, fun x hx => ?_⟩
      ext v
      rw [hρ s j x v, hβW j _ hx]
      simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, hE]
      congr 1
      funext i
      exact hDE j x (v i)
    constructor
    · exact hPA N N' m Λ Λ G Gs X ω (ρ 1) hG hXc hXm hXb hGs (fun j x _ => hDG j x)
        hGu.tendstoUniformlyOn (hend 1 Gs hH1 hDH1 ⟨zero_le_one, le_rfl⟩)
    · exact hPA N N' m Λ Λ F Fs X ω (ρ 0) hF hXc hXm hXb hFs (fun j x _ => hDF j x)
        hFu.tendstoUniformlyOn (hend 0 Fs hH0 hDH0 ⟨le_rfl, zero_le_one⟩)
  · intro Y hYc hYm hYb hYC
    refine hPA (N + 1) N' m L Λ' H Hs Y ω β hH hYc hYm hYb hHs ?_ (hHu.mono hYC) ?_
    · intro j y hy
      obtain ⟨t, ht, x, hx, rfl⟩ := hYC hy
      exact hDHb j t ht x hx
    · intro j
      exact ⟨W j, hWo j, hYC.trans (hCW j), hβW j⟩
  · intro Y hYc hYm hYb hYC
    refine hPA (N + 1) N' (m + 1) L Λ' H Hs Y (exteriorDerivativeTestOn (univ : Set (Euclid N')) m ω)
      (fun j => exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) m (β j)) hH hYc hYm hYb hHs ?_
      (hHu.mono hYC) ?_
    · intro j y hy
      obtain ⟨t, ht, x, hx, rfl⟩ := hYC hy
      exact hDHb j t ht x hx
    · intro j
      exact ⟨W j, hWo j, hYC.trans (hCW j), hdβW j⟩
  · intro j x hx t ht
    exact ⟨Hs j (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))),
      fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))),
      hβW j _ (hCW j ⟨t, ht, x, hx, rfl⟩), hDe j t x, hDJ j t ht x⟩

## Key steps

1. Smooth approximations F_j, G_j, H_j, Λ' from Submission.cmcdt_lpoh_smooth_approx; C(K) compact.
2. β_j from Submission.cmcdt_lpo_cutoff_pullback (β_j = H_j^#ω and dβ_j = H_j^#dω on open W_j ⊇ C); end slices ρ_{s,j} from conjunct (b) of Submission.cmcdt_lpo_slice_forms.
3. Near spt X, ρ_{1,j} = G_j^#ω and ρ_{0,j} = F_j^#ω (chain-rule identities H_j∘ι(s,·) = E_j, DH_j(ι(s,x))∘J = DE_j(x)); (PA) gives (ii).
4. (PA) for H with approximants H_j (derivative bound Λ' and uniform convergence on C ⊇ spt Y) gives (iii) for β_j and (iv) for dβ_j, dω.
5. On C, β_j(ι(t,x)) = ω(H_j(ι(t,x)))∘DH_j(ι(t,x)) with the derivative bounds (6), (7) of smooth_approx, giving (v).

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
