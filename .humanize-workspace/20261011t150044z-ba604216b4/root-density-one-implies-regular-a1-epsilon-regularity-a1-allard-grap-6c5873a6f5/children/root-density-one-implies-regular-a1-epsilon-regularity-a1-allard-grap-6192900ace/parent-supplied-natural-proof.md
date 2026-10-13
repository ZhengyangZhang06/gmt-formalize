# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1.interior_energy-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is step 4 of the parent proof (energy on interior balls). It uses the sibling child dorag_ha_lsc_grad_norm_sq.

1. (Cutoff.) Let s := (r + R)/2, so r < s < R. Let χ be the ContDiffBump centred at 0 with rIn = r and rOut = s. Then:
   - χ is C^∞ and 0 ≤ χ ≤ 1;
   - χ = 1 on closedBall(0, r);
   - tsupport χ = closedBall(0, s) ⊆ B;
   - χ has compact support.
2. (Test field.) Put Φ_i(x) := χ(x)·Dh(x)(e_i) for all x ∈ ℝⁿ. Since χ = 0 off closedBall(0, s) ⊆ B, this agrees with the parent's definition (χ_r·∂_ih on B, 0 off B).
   (a) Φ_i is C¹ on ℝⁿ.
       - h is C² on the open set B, so x ↦ Dh(x) is C¹ on B (ContDiffOn.fderiv_of_isOpen with 1 + 1 ≤ 2).
       - Hence x ↦ Dh(x)(e_i) is C¹ on B (ContDiffOn.clm_apply), and so is χ·Dh(·)(e_i). This gives C¹ at every x ∈ B.
       - If x ∉ B, then x ∉ tsupport χ, so χ vanishes near x. Hence Φ_i vanishes near x and is C¹ at x.
   (b) If Φ_i(x) ≠ 0 then χ(x) ≠ 0, so support Φ_i ⊆ support χ ⊆ closedBall(0, s). This ball is compact, so Φ_i has compact support (HasCompactSupport.intro), and tsupport Φ_i ⊆ closedBall(0, s) ⊆ B (closure_minimal).
   So Φ is admissible in the duality hypothesis.
3. (Pointwise identities.) By the first part of dorag_ha_lsc_grad_norm_sq, Σ_i (Dh(x)(e_i))² = ‖Dh(x)‖². Put g(x) := χ(x)‖Dh(x)‖². Then for every x:
   - Σ_i Dh(x)(e_i)·Φ_i(x) = χ(x)·Σ_i (Dh(x)(e_i))² = g(x);
   - Σ_i Φ_i(x)² = χ(x)²‖Dh(x)‖² ≤ χ(x)‖Dh(x)‖² = g(x), because 0 ≤ χ ≤ 1 gives χ² ≤ χ.
4. (Integrability.)
   - g is continuous on ℝⁿ. On B, χ is continuous and so is Dh, because h is C¹ on the open set B (ContDiffOn.continuousOn_fderiv_of_isOpen). At x ∉ B, g = 0 near x.
   - g has compact support, since support g ⊆ support χ. So g is integrable.
   - Σ_i Φ_i² is continuous with 0 ≤ Σ_i Φ_i² ≤ g, so it is integrable (Integrable.mono').
5. (The quantity X.) Let X := ∫_B g. Then X ≥ 0, since g ≥ 0. By step 3, ∫_B Σ_i Dh(e_i)Φ_i = X, and by steps 3–4, ∫_B Σ_i Φ_i² ≤ X (setIntegral_mono).
6. (Duality.) The hypothesis applied to Φ, monotonicity of √ and √E ≥ 0 give
   X ≤ √E·√(∫_B Σ_i Φ_i²) ≤ √E·√X.
7. (X ≤ E.) If X = 0 this is 0 ≤ E. If X > 0, then √X > 0, and √X·√X = X ≤ √E·√X gives √X ≤ √E. Hence X = (√X)² ≤ (√E)² = E, using E ≥ 0.
8. (Interior ball.)
   - For x ∈ B̆_r(0) ⊆ closedBall(0, r) we have χ(x) = 1, so ‖Dh(x)‖² = g(x). Hence ∫_{B̆_r(0)} ‖Dh‖² = ∫_{B̆_r(0)} g (setIntegral_congr_fun).
   - g ≥ 0 is integrable on B, and B̆_r(0) ⊆ B since r < R. So ∫_{B̆_r(0)} g ≤ ∫_B g = X (setIntegral_mono_set).
   Therefore ∫_{B̆_r(0)} ‖Dh‖² ≤ X ≤ E. ∎

Appendix (Lean proof, kernel-checked). This proof was compiled against the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c). It was placed inside `namespace GMT.Ch07` -> `namespace Submission` of a copy of GMT/Ch07/Submission.lean at b4d606d, after the `noncomputable section ... end` block and before `main_theorem`. The contract's `open`s are in scope there. `#print axioms` gives only propext, Classical.choice and Quot.sound. Sibling children are referenced by their bare names.

theorem dorag_ha_lsc_interior_energy : ∀ (n : ℕ) (R E r : ℝ) (h : Euclid n → ℝ), 0 < r → r < R → 0 ≤ E → ContDiffOn ℝ 2 h (ball (0 : Euclid n) R) → (∀ Φ : Fin n → Euclid n → ℝ, (∀ i, ContDiff ℝ 1 (Φ i)) → (∀ i, HasCompactSupport (Φ i)) → (∀ i, tsupport (Φ i) ⊆ ball (0 : Euclid n) R) → ∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) * Φ i x ≤ Real.sqrt E * Real.sqrt (∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, Φ i x ^ 2)) → ∫ x in ball (0 : Euclid n) r, ‖fderiv ℝ h x‖ ^ 2 ≤ E := by
  intro n R E r h hr hrR hE hh hdual
  set s := (r + R) / 2 with hs
  have hrs : r < s := by linarith
  have hsR : s < R := by linarith
  let χ : ContDiffBump (0 : Euclid n) := ⟨r, s, hr, hrs⟩
  have hχsupp : tsupport χ ⊆ ball (0 : Euclid n) R := by
    rw [χ.tsupport_eq]; exact closedBall_subset_ball hsR
  set Φ : Fin n → Euclid n → ℝ := fun i x => χ x * fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) with hΦdef
  have hDh : ContDiffOn ℝ 1 (fderiv ℝ h) (ball (0 : Euclid n) R) :=
    hh.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hΦC : ∀ i, ContDiff ℝ 1 (Φ i) := by
    intro i
    rw [contDiff_iff_contDiffAt]; intro x
    by_cases hx : x ∈ ball (0 : Euclid n) R
    · exact (χ.contDiff.contDiffOn.mul (hDh.clm_apply contDiffOn_const)).contDiffAt
        (isOpen_ball.mem_nhds hx)
    · have hxχ : x ∉ tsupport χ := fun h' => hx (hχsupp h')
      have hev : Φ i =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxχ] with y hy
        simp [Φ, hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hΦsupp : ∀ i, support (Φ i) ⊆ closedBall 0 s := by
    intro i x hx
    have hχx : χ x ≠ 0 := left_ne_zero_of_mul hx
    have hmem := subset_tsupport χ hχx
    rwa [χ.tsupport_eq] at hmem
  have hΦc : ∀ i, HasCompactSupport (Φ i) := fun i =>
    HasCompactSupport.intro (isCompact_closedBall 0 s) fun x hx =>
      notMem_support.1 fun h' => hx (hΦsupp i h')
  have hΦs : ∀ i, tsupport (Φ i) ⊆ ball (0 : Euclid n) R := fun i =>
    (closure_minimal (hΦsupp i) isClosed_closedBall).trans (closedBall_subset_ball hsR)
  have hgrad : ∀ x, ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) ^ 2 = ‖fderiv ℝ h x‖ ^ 2 :=
    fun x => ((dorag_ha_lsc_grad_norm_sq n (fderiv ℝ h x)).1).symm
  set g : Euclid n → ℝ := fun x => χ x * ‖fderiv ℝ h x‖ ^ 2 with hgdef
  have hpt1 : ∀ x, ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) * Φ i x = g x := by
    intro x
    simp only [Φ, g]
    rw [← hgrad x, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hpt2 : ∀ x, ∑ i : Fin n, Φ i x ^ 2 ≤ g x := by
    intro x
    have h0 : 0 ≤ χ x := χ.nonneg' x
    have h1 : χ x ≤ 1 := χ.le_one
    calc ∑ i : Fin n, Φ i x ^ 2 = χ x ^ 2 * ‖fderiv ℝ h x‖ ^ 2 := by
            simp only [Φ]; rw [← hgrad x, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ χ x * ‖fderiv ℝ h x‖ ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            nlinarith
      _ = g x := rfl
  have hgC : Continuous g := by
    rw [continuous_iff_continuousAt]; intro x
    by_cases hx : x ∈ ball (0 : Euclid n) R
    · have hcont : ContinuousOn g (ball (0 : Euclid n) R) :=
        χ.continuous.continuousOn.mul
          ((hh.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)).norm.pow 2)
      exact hcont.continuousAt (isOpen_ball.mem_nhds hx)
    · have hxχ : x ∉ tsupport χ := fun h' => hx (hχsupp h')
      have hev : g =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxχ] with y hy
        simp [g, hy]
      exact continuousAt_const.congr hev.symm
  have hgc : HasCompactSupport g := χ.hasCompactSupport.mul_right
  have hgI : Integrable g := hgC.integrable_of_hasCompactSupport hgc
  have hΦ2I : Integrable fun x => ∑ i : Fin n, Φ i x ^ 2 := by
    refine hgI.mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact (continuous_finsetSum _ fun i _ => ((hΦC i).continuous.pow 2)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      exact hpt2 x
  set X := ∫ x in ball (0 : Euclid n) R, g x with hXdef
  have hX0 : 0 ≤ X := setIntegral_nonneg measurableSet_ball fun x _ =>
    mul_nonneg (χ.nonneg' x) (sq_nonneg _)
  have hLHS : ∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) * Φ i x = X := by
    simp_rw [hpt1]; rfl
  have hRHS : ∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, Φ i x ^ 2 ≤ X :=
    setIntegral_mono hΦ2I.integrableOn hgI.integrableOn hpt2
  have hd := hdual Φ hΦC hΦc hΦs
  rw [hLHS] at hd
  have h1 : X ≤ Real.sqrt E * Real.sqrt X :=
    hd.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hRHS) (Real.sqrt_nonneg E))
  have hXE : X ≤ E := by
    rcases hX0.eq_or_lt with h0 | hpos
    · rw [← h0]; exact hE
    · have hsX : 0 < Real.sqrt X := Real.sqrt_pos.2 hpos
      have h2 : Real.sqrt X * Real.sqrt X ≤ Real.sqrt E * Real.sqrt X := by
        rw [Real.mul_self_sqrt hX0]; exact h1
      have h3 : Real.sqrt X ≤ Real.sqrt E := le_of_mul_le_mul_right h2 hsX
      calc X = Real.sqrt X ^ 2 := (Real.sq_sqrt hX0).symm
        _ ≤ Real.sqrt E ^ 2 := by gcongr
        _ = E := Real.sq_sqrt hE
  have hball : ∫ x in ball (0 : Euclid n) r, ‖fderiv ℝ h x‖ ^ 2 = ∫ x in ball (0 : Euclid n) r, g x := by
    refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
    simp [g, χ.one_of_mem_closedBall (ball_subset_closedBall hx)]
  have hmono : ∫ x in ball (0 : Euclid n) r, g x ≤ X :=
    setIntegral_mono_set hgI.integrableOn
      (ae_of_all _ fun x => mul_nonneg (χ.nonneg' x) (sq_nonneg _))
      (ball_subset_ball hrR.le).eventuallyLE
  linarith

## Key steps

1. Bump χ with 0 ≤ χ ≤ 1, χ = 1 on closedBall(0, r), and tsupport χ = closedBall(0, (r + R)/2) ⊆ B.
2. Φ_i := χ·∂_ih is C¹ (since h ∈ C²(B)) and compactly supported in B, so it is admissible.
3. By the gradient identity, ∇h·Φ = χ‖Dh‖² =: g and |Φ|² = χ²‖Dh‖² ≤ g.
4. X := ∫_B g satisfies X ≤ √E·√X, so X ≤ E; and ∫_{B̆_r} ‖Dh‖² = ∫_{B̆_r} g ≤ X.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; cmp GMT/Ch07/Contract.lean <snapshot>/project/GMT/Ch07/Contract.lean  (both IDENTICAL; git HEAD b4d606d)`
- `sed -n 150,200p Analysis/Calculus/Rademacher.lean; rg -n 'theorem|lemma' Analysis/Calculus/Rademacher.lean  (LipschitzWith.integral_lineDeriv_mul_eq :169, LipschitzWith.ae_differentiableAt :385)`
- `rg -n 'theorem (ContDiff.lipschitzWith_of_hasCompactSupport|exists_pos_lt_subset_ball|exists_lt_subset_ball|support_fderiv_subset|norm_fderiv_le_of_lipschitz|measurable_fderiv|measurable_fderiv_apply_const|integral_mul_le_Lp_mul_Lq_of_nonneg|ContDiffOn.fderiv_of_isOpen|ContDiffOn.continuousOn_fderiv_of_isOpen)' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem (one_of_mem_closedBall|support_eq|tsupport_eq|nonneg|nonneg.|le_one|contDiff|hasCompactSupport)' Analysis/Calculus/BumpFunction/Basic.lean; rg -n hasContDiffBump_of_innerProductSpace Analysis/`
- `rg -n 'setLIntegral_iUnion_of_directed|restrict_iUnion_apply_eq_iSup|lintegral_iSup|lintegral_iUnion' MeasureTheory`
- `rg -n 'toDual_symm_apply|EuclideanSpace.(norm_eq|norm_sq_eq|real_norm_sq_eq|inner_single_left|single_apply)' Analysis/InnerProductSpace; rg -n sum_mul_le_sqrt_mul_sqrt Analysis/Real/Sqrt.lean; rg -n two_two Basic/Real/ConjExponents.lean`
- `rg -n 'MemLp.of_bound|Integrable.of_bound|Integrable.mul_bdd|Integrable.bdd_mul|abs_integral_le_integral_abs|norm_integral_le_of_norm_le|fderiv_of_notMem_tsupport|notMem_mulTSupport_iff_eventuallyEq|Continuous.bounded_above_of_compact_support|IntegrableOn.of_forall_sdiff_eq_zero|integral_finsetSum|isFiniteMeasure_restrict|measure_ball_lt_top|isCompact_iUnion|Filter.EventuallyEq.fderiv_eq|DifferentiableAt.lineDeriv_eq_fderiv' <snapshot>/mathlib/Mathlib`
- `rg -l 'integral_lineDeriv_mul_eq|lineDeriv' <snapshot>/project  (no match); rg -l 'integral_lineDeriv_mul_eq|ContDiffBump|setLIntegral_iUnion_of_directed|toDual_symm_apply' .lake/packages/simongmt  (only mollifier/Whitney-bump/L1-dual uses, no IBP lemma); rg -n -i 'theorem .*(ibp|integration_by_parts|divergence)' .lake/packages/simongmt  (only varifold tangential-divergence lemmas)`
- `python3 -I scan of every lean_name in dag.json, nodes/*/*.json and issue-workers.json (566 names) for the 6 proposed dorag_ha_lsc_* names (no collision); sibling node statements printed from dag.json (all siblings still decomposing, none reusable)`
- `python3 -I import of verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') to replay the comparator child scope`
- `lean (toolchains/lean-4.35.0-rc3-linux/bin/lean; LEAN_PATH = workspace .lake/build + .lake/packages builds): /tmp/energylsc-decomp/Children.lean (stubs + parent assembly), ChildB.lean, ChildAF.lean, ChildBC.lean, ChildAFE.lean, ChildD.lean, Full2.lean (#print axioms), Challenge.lean (exact comparator challenge scope), insitu/ (modified Submission compiled with `lean --root=src -o build/GMT/Ch07/Submission.olean` + NodeSolution `exact Submission.X` checks)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-6c5873a6f5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/Real/ConjExponents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/tmp/energylsc-decomp/Full2.lean`
- `/tmp/energylsc-decomp/Challenge.lean`
- `/tmp/energylsc-decomp/insitu/src/GMT/Ch07/Submission.lean`
- `/tmp/energylsc-decomp/insitu/NodeSolution.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. GMT/Ch07/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

The pinned Mathlib supplies every tool the children need:
- Lipschitz integration by parts and Rademacher: LipschitzWith.integral_lineDeriv_mul_eq, LipschitzWith.ae_differentiableAt, DifferentiableAt.lineDeriv_eq_fderiv;
- C¹_c ⇒ Lipschitz: ContDiff.lipschitzWith_of_hasCompactSupport (its argument is `n ≠ 0`);
- bump functions on Euclid n: ContDiffBump with one_of_mem_closedBall, tsupport_eq, nonneg', le_one, hasCompactSupport and contDiff;
- exists_pos_lt_subset_ball;
- the Riesz isometry: InnerProductSpace.toDual_symm_apply, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.inner_single_left;
- finite Cauchy–Schwarz: Real.sum_mul_le_sqrt_mul_sqrt;
- Hölder: integral_mul_le_Lp_mul_Lq_of_nonneg with Real.HolderConjugate.two_two;
- monotone exhaustion: setLIntegral_iUnion_of_directed;
- MemLp.of_bound, Integrable.of_bound, Integrable.mul_bdd, Integrable.bdd_mul, fderiv_of_notMem_tsupport, notMem_tsupport_iff_eventuallyEq and integral_finsetSum (integral_finset_sum is deprecated).

Nothing is reusable from the project or SimonGMT. The project has no lineDeriv/IBP lemma. SimonGMT uses ContDiffBump only for mollifiers and Whitney bumps, and its divergence results are varifold tangential-divergence lemmas. No comparator-accepted declaration has an identical type, and the six dorag_ha_lsc_* names are unreserved.

Lean results:
- every child type elaborates in the comparator's replayed scope;
- all six children are fully proved;
- the exact frozen parent type follows from them;
- in-situ NodeSolution checks (`exact Submission.X`) against a compiled copy of GMT.Ch07.Submission pass, with axioms [propext, Classical.choice, Quot.sound] only.
