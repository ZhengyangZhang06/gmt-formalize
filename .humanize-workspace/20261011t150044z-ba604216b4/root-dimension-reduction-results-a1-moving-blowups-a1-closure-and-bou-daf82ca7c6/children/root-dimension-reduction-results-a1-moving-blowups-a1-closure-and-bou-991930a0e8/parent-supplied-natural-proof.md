# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.boundary_im-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.boundary_im-a1.deformation_closure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 7–9 of the parent proof of dmcbr_boundary_isIntegerMultiplicity (Simon, Introduction to GMT, Ch. 6: 6.2, first case U = ℝ^{n+ℓ} with M(T), M(∂T) < ∞ — the scaled deformation theorem 5.3 with ρ = ρ_k ↓ 0 gives P_k ⇀ T with M(∂P_k) ≤ cM(∂T); 6.3 — combine this with the closure theorem). Uses the siblings cmr_abs_apply_le_massOn (key eval_bound) and rsd_mw_tfa_norm_props (key norm_props; part (iv), continuity of |·| = covectorEuclideanNorm). Both are comparator-accepted declarations reused at their frozen types. All masses are taken in the domain ℝ^P, so M(X) = M_{ℝ^P}(X) = X.massOn univ. The degree of the closure statement used is d, one less than the degree d + 1 of T, so nothing about degree d + 1 is assumed.
1. Constants. (DT) with (P, m := d) gives c ∈ ℝ≥0 with c ≥ 1. Let Λ := M(T) ∈ ℝ≥0; this is possible because M(T) is finite, and then M(T) ≤ Λ (ENNReal.coe_toNNReal).
2. Approximants. For k ∈ ℕ put ρ_k := 2^{−k} > 0. Apply (DT) with ρ_k, K and Λ to T; T is integer multiplicity, spt T ⊆ K, M(T) ≤ Λ and M(∂T) < ∞. This gives Q_k, S_k ∈ 𝒟_{d+1}(ℝ^P) and R_k ∈ 𝒟_{d+2}(ℝ^P) such that ∂Q_k is integer multiplicity, T − Q_k − S_k = ∂R_k, M(∂Q_k) ≤ cM(∂T), M(R_k) ≤ cρ_kM(T) and M(S_k) ≤ cρ_kM(∂T). Choose such currents for every k.
3. Sup bounds for test forms. Let m ∈ ℕ and ω ∈ 𝒟^m(ℝ^P). The function x ↦ |ω(x)| is continuous, because |·| is continuous by rsd_mw_tfa_norm_props (iv) and ω is smooth. It has compact support, because ω does and |0| = 0 (HasCompactSupport.comp_left). So it is bounded (HasCompactSupport.exists_bound_of_continuous). Taking the maximum of a bound with 1 gives C_ω > 0 with |ω(x)| ≤ C_ω for every x.
4. Weak convergence Q_k ⇀ T (Step 8 of the parent proof). Fix ω ∈ 𝒟^{d+1}(ℝ^P) and put C₁ := C_ω and C₂ := C_{dω}, where dω ∈ 𝒟^{d+2}(ℝ^P).
 - Subtraction of currents is pointwise, so evaluating T − Q_k − S_k = ∂R_k at ω gives T(ω) − Q_k(ω) − S_k(ω) = ∂R_k(ω) = R_k(dω). Hence |Q_k(ω) − T(ω)| ≤ |S_k(ω)| + |R_k(dω)|.
 - M(S_k) ≤ cρ_kM(∂T) < ∞ and M(R_k) ≤ cρ_kM(T) < ∞. So cmr_abs_apply_le_massOn with W := ℝ^P gives |S_k(ω)| ≤ C₁·M(S_k) and |R_k(dω)| ≤ C₂·M(R_k), with the finite masses read as real numbers. In [0, ∞] this reads ofReal|S_k(ω)| ≤ ofReal(C₁)·M(S_k) ≤ ofReal(C₁)·cρ_kM(∂T) and ofReal|R_k(dω)| ≤ ofReal(C₂)·M(R_k) ≤ ofReal(C₂)·cρ_kM(T) (ENNReal.ofReal_mul, ENNReal.ofReal_toReal).
 - So ofReal|Q_k(ω) − T(ω)| ≤ ofReal(ρ_k)·A with A := C₁cM(∂T) + C₂cM(T) < ∞. Taking toReal (ENNReal.toReal_mono) gives |Q_k(ω) − T(ω)| ≤ ρ_k·A.toReal.
 - The right side tends to 0 as k → ∞ (tendsto_pow_atTop_nhds_zero_of_lt_one, squeeze_zero). Hence Q_k(ω) → T(ω) for every ω, i.e. Q_k ⇀ T in ℝ^P.
5. Boundaries. ∂Q_k ⇀ ∂T in ℝ^P (WeaklyConvergesOn.boundary; Simon 2.3 and 2.13).
6. Uniform local bounds (Step 9 of the parent proof). Let W be open.
 - M_W(∂Q_k) ≤ M_{ℝ^P}(∂Q_k) = M(∂Q_k) ≤ cM(∂T) (GeometricCurrentOn.massOn_mono).
 - boundaryMassOn(∂Q_k, W) = 0. If d = 0, this holds by definition: the boundary mass of a 0-current is 0. If d = m + 1, it equals M_W(∂∂Q_k) = M_W(0) by GeometricCurrentOn.boundary_boundary, and M_W(0) = 0 because every admissible value is ofReal(0) = 0.
 Hence sup_k (M_W(∂Q_k) + boundaryMassOn(∂Q_k, W)) ≤ cM(∂T) < ∞, since c < ∞ and M(∂T) < ∞ (ENNReal.mul_lt_top).
7. Closure. Apply CL(d) with P, U := ℝ^P (open), T_k := ∂Q_k (integer multiplicity by step 2), the bound of step 6 and the convergence of step 5. Hence ∂T is integer multiplicity. ∎

Lean note (verified realization of the numbered proof above; not part of the proof). The following tactic proof of `Submission.dmcbr_bim_boundary_im_of_compact_support` compiles against the frozen contract (Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b366308). It is placed after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open` commands, with only the two declared sibling declarations `Submission.cmr_abs_apply_le_massOn` and `Submission.rsd_mw_tfa_norm_props` (their accepted proofs) in scope. `#print axioms` reports only propext, Classical.choice and Quot.sound, and `exact Submission.dmcbr_bim_boundary_im_of_compact_support` closes the frozen type in the comparator scope. Do not open the ContDiff scope, whose notation makes ω a token; smoothness is written ContDiff ℝ (⊤ : ℕ∞).
```lean
  have massOn_zero_aux : ∀ {P m : ℕ} {U : Set (Euclid P)} (W : Set (Euclid P)),
      (0 : GeometricCurrentOn U m).massOn W = 0 := by
    intro P m U W
    apply le_antisymm _ bot_le
    apply sSup_le
    rintro _ ⟨ω, -, rfl⟩
    simp
  have boundaryMassOn_boundary_aux : ∀ {P : ℕ} {U : Set (Euclid P)} (k : ℕ)
      (Z : GeometricCurrentOn U (k + 1)) (W : Set (Euclid P)), boundaryMassOn Z.boundary W = 0 := by
    intro P U k Z W
    cases k with
    | zero => rfl
    | succ m =>
      change Z.boundary.boundary.massOn W = 0
      rw [GeometricCurrentOn.boundary_boundary]
      exact massOn_zero_aux W
  intro hDT d hCL P T K hK hT hTK hm hbm
  obtain ⟨c, -, hc⟩ := hDT P d
  set Λ : NNReal := T.mass.toNNReal with hΛdef
  have hΛ : T.mass ≤ Λ := by rw [hΛdef, ENNReal.coe_toNNReal hm.ne]
  have hρ : ∀ k : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ k := fun k => by positivity
  choose 𝒬 _ h𝒬 using fun k : ℕ => hc ((1 / 2 : ℝ) ^ k) K Λ (hρ k) hK
  choose Q _ R S _ hQb _ hEq _ _ hQbm hRm hSm _ _ using fun k => h𝒬 k T hT hTK hΛ hbm
  -- a uniform bound for the Euclidean coefficient norm of a test form
  have hbound : ∀ {m : ℕ} (ω : TestFormOn (univ : Set (Euclid P)) m), ∃ C : ℝ, 0 < C ∧
      ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) m) x) ≤ C := by
    intro m ω
    have hω1 : IsSmoothForm (ω : DifferentialForm (Euclid P) m) := ω.property.1.1
    have hω2 : HasCompactSupport (ω : DifferentialForm (Euclid P) m) := ω.property.1.2
    have hωc : Continuous (ω : DifferentialForm (Euclid P) m) := hω1.continuous
    have hcont : Continuous fun x => covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) m) x) :=
      (Submission.rsd_mw_tfa_norm_props P m).2.2.2.comp hωc
    have hcs : HasCompactSupport fun x => covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) m) x) :=
      hω2.comp_left (g := fun α : Covector (Euclid P) m => covectorEuclideanNorm α)
        (covectorEuclideanNorm_zero P m)
    obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hcont
    refine ⟨max C 1, lt_max_of_lt_right one_pos, fun x => ?_⟩
    exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hC x).trans (le_max_left _ _))
  have hconv : WeaklyConvergesOn Q T := by
    intro ω
    obtain ⟨C₁, hC₁, hb₁⟩ := hbound ω
    obtain ⟨C₂, hC₂, hb₂⟩ := hbound (exteriorDerivativeTestOn univ (d + 1) ω)
    set A : ℝ≥0∞ := ENNReal.ofReal C₁ * ((c : ℝ≥0∞) * T.boundary.mass) +
      ENNReal.ofReal C₂ * ((c : ℝ≥0∞) * T.mass) with hA
    have hAfin : A ≠ ∞ := by
      rw [hA]
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.coe_ne_top hbm.ne), ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.coe_ne_top hm.ne)⟩
    have hkey : ∀ k, |Q k ω - T ω| ≤ (1 / 2 : ℝ) ^ k * A.toReal := by
      intro k
      have e : T ω - Q k ω - S k ω = R k (exteriorDerivativeTestOn univ (d + 1) ω) := by
        have := congrArg (fun Z : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1) => Z ω) (hEq k)
        exact this
      have hS : (S k).massOn univ ≤ (c : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ k) * T.boundary.mass :=
        hSm k
      have hR : (R k).massOn univ ≤ (c : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ k) * T.mass := hRm k
      have hSfin : (S k).massOn univ ≠ ∞ := ne_top_of_le_ne_top
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hbm.ne) hS
      have hRfin : (R k).massOn univ ≠ ∞ := ne_top_of_le_ne_top
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hm.ne) hR
      -- evaluation bound |X(φ)| ≤ C·M(X) (cmr_abs_apply_le_massOn), in ℝ≥0∞
      have h1 : ENNReal.ofReal |S k ω| ≤ ENNReal.ofReal C₁ * (S k).massOn univ := by
        have h := Submission.cmr_abs_apply_le_massOn P (d + 1) univ univ (S k) ω C₁ hSfin
          (subset_univ _) hb₁
        calc ENNReal.ofReal |S k ω| ≤ ENNReal.ofReal (C₁ * ((S k).massOn univ).toReal) :=
              ENNReal.ofReal_le_ofReal h
          _ = ENNReal.ofReal C₁ * (S k).massOn univ := by
              rw [ENNReal.ofReal_mul hC₁.le, ENNReal.ofReal_toReal hSfin]
      have h2 : ENNReal.ofReal |R k (exteriorDerivativeTestOn univ (d + 1) ω)| ≤
          ENNReal.ofReal C₂ * (R k).massOn univ := by
        have h := Submission.cmr_abs_apply_le_massOn P (d + 2) univ univ (R k)
          (exteriorDerivativeTestOn univ (d + 1) ω) C₂ hRfin (subset_univ _) hb₂
        calc ENNReal.ofReal |R k (exteriorDerivativeTestOn univ (d + 1) ω)| ≤
              ENNReal.ofReal (C₂ * ((R k).massOn univ).toReal) := ENNReal.ofReal_le_ofReal h
          _ = ENNReal.ofReal C₂ * (R k).massOn univ := by
              rw [ENNReal.ofReal_mul hC₂.le, ENNReal.ofReal_toReal hRfin]
      have hle : ENNReal.ofReal |Q k ω - T ω| ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) * A := by
        have habs : |Q k ω - T ω| ≤ |S k ω| + |R k (exteriorDerivativeTestOn univ (d + 1) ω)| := by
          rw [← e]
          calc |Q k ω - T ω| = |-(S k ω) - (T ω - Q k ω - S k ω)| := by ring_nf
            _ ≤ |-(S k ω)| + |T ω - Q k ω - S k ω| := abs_sub _ _
            _ = |S k ω| + |T ω - Q k ω - S k ω| := by rw [abs_neg]
        calc ENNReal.ofReal |Q k ω - T ω|
            ≤ ENNReal.ofReal |S k ω| + ENNReal.ofReal |R k (exteriorDerivativeTestOn univ (d + 1) ω)| :=
              (ENNReal.ofReal_le_ofReal habs).trans ENNReal.ofReal_add_le
          _ ≤ ENNReal.ofReal C₁ * ((c : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ k) * T.boundary.mass) +
              ENNReal.ofReal C₂ * ((c : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ k) * T.mass) := by
              gcongr
              · exact h1.trans (by gcongr)
              · exact h2.trans (by gcongr)
          _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ k) * A := by rw [hA]; ring
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin) hle
      rwa [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (hρ k).le] at this
    rw [tendsto_iff_dist_tendsto_zero]
    have hlim : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k * A.toReal) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const A.toReal
    exact squeeze_zero (fun k => dist_nonneg) (fun k => by rw [Real.dist_eq]; exact hkey k) hlim
  refine hCL P univ (fun k => (Q k).boundary) T.boundary isOpen_univ hQb ?_ hconv.boundary
  intro W _ _
  refine lt_of_le_of_lt (b := (c : ℝ≥0∞) * T.boundary.mass) (iSup_le fun k => ?_)
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hbm)
  rw [boundaryMassOn_boundary_aux d (Q k) W, add_zero]
  exact ((Q k).boundary.massOn_mono (subset_univ W)).trans (hQbm k)
```

## Key steps

1. Apply (DT) with ρ_k = 2^{−k}, K and Λ = M(T): T − Q_k − S_k = ∂R_k with ∂Q_k IM, M(∂Q_k) ≤ cM(∂T), M(R_k) ≤ cρ_kM(T), M(S_k) ≤ cρ_kM(∂T).
2. For each test form ω, |Q_k(ω) − T(ω)| ≤ |S_k(ω)| + |R_k(dω)| ≤ ρ_k·c(C_ω M(∂T) + C_{dω} M(T)) → 0 by cmr_abs_apply_le_massOn and the sup bound from rsd_mw_tfa_norm_props (iv), so Q_k ⇀ T and ∂Q_k ⇀ ∂T.
3. M_W(∂Q_k) ≤ cM(∂T) and boundaryMassOn(∂Q_k, W) = 0 (∂∂ = 0), so the hypotheses of CL(d) in U = ℝ^P hold and ∂T is IM.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean; cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean`
- `python3 scans of RUN/dag.json: selected node and its siblings convergence_tools-a1 / im_local-a1 (frozen types, status); the five parent-dependency types against the hypotheses of the selected type (dimred_mbl_current_foundations == (REP) ∧ (IMC) byte-for-byte); lean_name lookups for rsd_mw_tfa_norm_props, cmr_abs_apply_le_massOn, lcmp_massOn_le_of_vanish_off_compact, lcmp_imRep_measure_restrict, dtc_extend_by_zero (each unique, status accepted, candidate commit set), cbr_bim_* (status decomposing, other parent) and dmcbr_bim_* (no node); identical-type search for the three new statements; dmcbr_isIntegerMultiplicity_of_local type == cbr_isIntegerMultiplicity_of_local type`
- `python3 difflib comparison of the parent-supplied proofs in RUN/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-10c568d35f and RUN/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-daf82ca7c6; reading decomposition-v3.json and decomposition-audit-v1..v3.json of the former`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint|def _solve_children' /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py; sed -n 179,215p /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `git show <commit>:GMT/Ch07/Submission.lean and git diff <commit>^ <commit> for f492ba4a, 7a706164, a3cc98d1, ae810e9b, 2527748d (extraction of the accepted proofs; reused types compared byte-for-byte)`
- `rg -c dmcbr_bim SNAPSHOT (no match, exit 1); rg -c dmcbr_bim GMT (no match, exit 1); rg -n 'dmcbr_bim|cbr_bim' SNAPSHOT/project/GMT (no match, exit 1)`
- `rg -n -i 'boundary rectifiab|BoundaryRectif|deformation|closure theorem|isIntegerMultiplicity_boundary|boundary_isIntegerMultiplicity' SNAPSHOT/project/GMT -g '*.lean' (matches only GMT/Ch06 Contract/Submission defs DeformationTheorem, BoundaryRectifiability and GMT/Ch02 IsAdmissibleDeformation); cmp SNAPSHOT/project/GMT/Ch06/Submission.lean SNAPSHOT/project/GMT/Ch06/Contract.lean (identical, main_theorem unproved)`
- `rg -n -F over SNAPSHOT/mathlib/Mathlib: theorem enorm_integral_le_lintegral_enorm, theorem lintegral_indicator_one_le, theorem setIntegral_eq_integral_of_forall_compl_eq_zero, theorem setLIntegral_congr_fun, theorem withDensity_apply, theorem volume_Ioo, theorem dist_left, theorem isCompact_sphere, theorem ofReal_add_le, theorem ae_restrict_of_ae, theorem tendsto_pow_atTop_nhds_zero_of_lt_one, lemma squeeze_zero, lemma HasCompactMulSupport.exists_bound_of_continuous (all found)`
- `rg -l -F over .lake/packages/simongmt/Poincare: theorem WeaklyConvergesOn.boundary, theorem GeometricCurrentOn.boundary_boundary, theorem tsupport_exteriorDerivative_subset, theorem GeometricCurrentOn.massOn_mono, theorem GeometricCurrentOn.le_massOn, theorem GeometricCurrentOn.restrictDomain_apply, def testFormOnInclusion, theorem covectorEuclideanNorm_zero (all found)`
- `grep/sed on book/chapter-06.txt for Simon 4.5 (slicing lemma), 5.3 (scaled deformation theorem), 6.2 (weak polyhedral approximation), 6.3 (boundary rectifiability)`
- `lake env lean (v4.35.0-rc3) on /tmp/dmcbr-bim-split/lean/Challenge_*.lean (8 comparator challenges), /tmp/dmcbr-bim-split/lean/AllProofs.lean (accepted proofs + new children + assembly + exact-solution checks + #print axioms) and /tmp/dmcbr-bim-split/lean/Isolated_dmcbr_bim_*.lean (3 files); lean_contract.validate_lean_statement on all 8 types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-daf82ca7c6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-4c4627e694/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-10c568d35f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-10c568d35f/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-10c568d35f/decomposition-audit-v3.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/tmp/dmcbr-bim-split/lean/AllProofs.lean`
- `/tmp/dmcbr-bim-split/lean/Isolated_dmcbr_bim_slice_localization.lean`
- `/tmp/dmcbr-bim-split/lean/Isolated_dmcbr_bim_extension_mass_bounds.lean`
- `/tmp/dmcbr-bim-split/lean/Isolated_dmcbr_bim_boundary_im_of_compact_support.lean`

Pins match: workspace HEAD b4d606d is the snapshot project commit, Mathlib is 25730c7c and SimonGMT is 2b366308. Submission.lean is byte-identical to the frozen contract and to the snapshot copy. The snapshot project has no dmcbr_bim or cbr_bim declaration and no proved boundary-rectifiability, closure or deformation theorem: GMT/Ch06/Contract.lean states DeformationTheorem (5.3) and BoundaryRectifiability (6.3) only as Prop definitions in namespace GMT.Ch06, over that chapter's own definitions, and its Submission.lean equals the contract (main_theorem unproved), so nothing there is reusable. The SimonGMT Chapter 6 API used by the child proofs (massOn, le_massOn, massOn_mono, boundary_boundary, WeaklyConvergesOn.boundary, restrictDomain, testFormOnInclusion, tsupport_exteriorDerivative_subset) is present. Every Mathlib lemma cited by the child proofs exists in the pinned sources. The DAG node cbr_boundary_isIntegerMultiplicity has a byte-identical frozen type and an audited split of this shape; its three new children are unaccepted and owned by another parent, so they are restated here under the fresh names dmcbr_bim_*, which match no DAG node or file. The five reused declarations are unique, accepted, with candidate commits, at byte-identical types. All 8 child types elaborate as comparator challenges. The 3 new child proofs compile with only their declared siblings. The hypothesis-only assembly proves the exact parent type from the children and the frozen type of dmcbr_isIntegerMultiplicity_of_local, with axioms propext, Classical.choice and Quot.sound.
