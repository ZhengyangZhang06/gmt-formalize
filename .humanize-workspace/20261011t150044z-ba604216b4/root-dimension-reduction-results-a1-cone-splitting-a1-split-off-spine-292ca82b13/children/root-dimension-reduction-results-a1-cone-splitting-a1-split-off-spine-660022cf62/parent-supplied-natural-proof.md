# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_param-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_param-a1.cone_map-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 1, 2, 3(a) and 4 of the selected parent proof (the cone parametrization H_i(s, u) = s·G_i(u)), stated for one Lipschitz map G and an arbitrary radius ρ. This parametrizes Simon's cone 0 ⨯ T = h_#([[(0,1)]] × T), h(t, x) = tx (Ch. 6, 2.30, chapter-06.txt lines 525–536).
Notation. π₀ : ℝ^{n+1} → ℝ, π₀(z) := z_0 (EuclideanSpace.proj 0), and π′ : ℝ^{n+1} → ℝ^n, π′(z) := tail z. π′ is linear (additivity and homogeneity hold definitionally), so both are continuous linear maps (LinearMap.toContinuousLinearMap on the finite-dimensional ℝ^{n+1}) and hence Lipschitz with constants ‖π₀‖ and ‖π′‖. On the standard basis: π₀ê_0 = 1, π′ê_0 = 0, π₀ê_{a+1} = 0 and π′ê_{a+1} = e_a. This follows by comparing coordinates: (ê_b)_j = [j = b], Fin.tail shifts indices by Fin.succ, Fin.succ is injective and Fin.succ a ≠ 0.

1. (Radius.) Put ρ′ := max(ρ, 1). Then ρ′ > 0 and ρ′ ≥ ρ.
2. (Retraction.) Let φ be the ContDiffBump centered at 0 ∈ ℝ^P with rIn = ρ′ and rOut = ρ′ + 1 (valid since 0 < ρ′ < ρ′ + 1), and r(y) := φ(y)·y.
 (a) r is C¹, as the product of the smooth φ and the identity, and has compact support because φ does (HasCompactSupport.smul_right). Hence r is Lipschitz with some constant K_r (ContDiff.lipschitzWith_of_hasCompactSupport).
 (b) ‖r(y)‖ ≤ ρ′ + 1 for all y. If ‖y‖ < ρ′ + 1, then ‖r(y)‖ = |φ(y)|·‖y‖ ≤ 1·(ρ′ + 1) since 0 ≤ φ ≤ 1. Otherwise dist(y, 0) ≥ rOut, so φ(y) = 0 (ContDiffBump.zero_of_le_dist) and r(y) = 0.
 (c) r(y) = y whenever ‖y‖ ≤ ρ′, because φ = 1 on closedBall(0, rIn) (ContDiffBump.one_of_mem_closedBall).
3. (Clamp.) σ(s) := max(0, min(s, 1)). σ is 1-Lipschitz (s ↦ min(s, 1) and t ↦ max(0, t) are 1-Lipschitz), 0 ≤ σ ≤ 1 so |σ(s)| ≤ 1, and σ(s) = s for s ∈ (0, 1).
4. (Definition.) H(z) := σ(z_0)·r(G(tail z)).
5. (H is Lipschitz.) Put f₁(z) := σ(π₀z) and f₂(z) := r(G(π′z)). f₁ is ‖π₀‖-Lipschitz with |f₁| ≤ 1, and f₂ is K_r·L·‖π′‖-Lipschitz with ‖f₂‖ ≤ ρ′ + 1 (steps 2 and 3). For z, z′ ∈ ℝ^{n+1}, H(z) − H(z′) = (f₁(z) − f₁(z′))·f₂(z) + f₁(z′)·(f₂(z) − f₂(z′)). Hence
 ‖H(z) − H(z′)‖ ≤ |f₁(z) − f₁(z′)|·‖f₂(z)‖ + |f₁(z′)|·‖f₂(z) − f₂(z′)‖ ≤ ((ρ′ + 1)·‖π₀‖ + K_r·L·‖π′‖)·‖z − z′‖,
 so H is Lipschitz with constant K := ((ρ′ + 1)‖π₀‖ + K_r L ‖π′‖)₊ (LipschitzWith.of_dist_le').
6. (Local form; part (a).) Fix z with z_0 ∈ (0, 1) and ‖G(tail z)‖ < ρ. Let H̃(z′) := π₀(z′)·G(π′z′) and O := {z′ : π₀z′ ∈ (0, 1), ‖G(π′z′)‖ < ρ′}. O is open, as the intersection of the preimages of the open sets (0, 1) and (−∞, ρ′) under continuous maps (G is continuous because it is Lipschitz). z ∈ O because ‖G(tail z)‖ < ρ ≤ ρ′. For z′ ∈ O, σ(z′_0) = z′_0 by step 3 and r(G(tail z′)) = G(tail z′) by step 2(c), since ‖G(tail z′)‖ < ρ′. So H = H̃ on the neighbourhood O of z, i.e. H =ᶠ[𝓝 z] H̃. In particular H(z) = z_0·G(tail z), which is (a).
7. (Derivative.) Assume G is differentiable at u := tail z. π₀ and π′ are continuous linear, so G∘π′ has derivative DG(u)∘π′ at z (chain rule). By the product rule (HasFDerivAt.smul), H̃ has at z the derivative D := z_0·(DG(u)∘π′) + π₀.smulRight(G(u)), that is D(v) = z_0·DG(u)(π′v) + (π₀v)·G(u). Since H =ᶠ[𝓝 z] H̃, DH(z) = DH̃(z) = D (Filter.EventuallyEq.fderiv_eq, HasFDerivAt.fderiv).
8. (Evaluation on the basis; part (b).) From π₀ê_0 = 1 and π′ê_0 = 0 we get D(ê_0) = z_0·DG(u)(0) + 1·G(u) = G(u). From π₀ê_{a+1} = 0 and π′ê_{a+1} = e_a we get D(ê_{a+1}) = z_0·DG(u)e_a. By Fin.cases on b ∈ Fin (n+1) (Fin.cons_zero, Fin.cons_succ), the tuple (b ↦ DH(z)ê_b) equals Fin.cons (G(u)) (a ↦ z_0·DG(u)e_a), which is (b). ∎

Appendix (supplementary; the numbered argument above is complete without it). The following Lean proof of exactly this frozen statement was checked during decomposition with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c) after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's opens, with the declaration named Submission.dimred_cs_sos_cfs_cp_cone_map as in accepted nodes. It uses no sibling declaration. Its axioms are propext, Classical.choice and Quot.sound only.
Lean tactic block for `theorem Submission.dimred_cs_sos_cfs_cp_cone_map`, whose type is exactly the frozen lean_statement of this child (it follows `:= by`):
  intro P n G L ρ hG
  -- step 1: a Lipschitz, bounded `r` with `r = id` on `closedBall 0 ρ'`, `ρ' := max ρ 1`
  set ρ' : ℝ := max ρ 1 with hρ'
  have hρ'pos : 0 < ρ' := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨r, ⟨Kr, hKr⟩, hr_bound, hr_id⟩ : ∃ r : Euclid P → Euclid P, (∃ K : NNReal, LipschitzWith K r) ∧
      (∀ y, ‖r y‖ ≤ ρ' + 1) ∧ (∀ y : Euclid P, ‖y‖ ≤ ρ' → r y = y) := by
    let φ : ContDiffBump (0 : Euclid P) := ⟨ρ', ρ' + 1, hρ'pos, by linarith⟩
    refine ⟨fun y => φ y • y, ?_, ?_, ?_⟩
    · have hr_smooth : ContDiff ℝ 1 (fun y : Euclid P => φ y • y) := φ.contDiff.smul contDiff_id
      have hr_supp : HasCompactSupport (fun y : Euclid P => φ y • y) := φ.hasCompactSupport.smul_right
      exact ContDiff.lipschitzWith_of_hasCompactSupport hr_supp hr_smooth (by simp)
    · intro y
      by_cases hy : ‖y‖ < ρ' + 1
      · calc ‖φ y • y‖ = |φ y| * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ ≤ 1 * (ρ' + 1) := by
            gcongr
            · rw [abs_of_nonneg φ.nonneg]; exact φ.le_one
          _ = ρ' + 1 := one_mul _
      · have h0 : φ y = 0 := φ.zero_of_le_dist (by simpa [dist_zero_right] using not_lt.mp hy)
        simp [h0]; linarith
    · intro y hy
      have : φ y = 1 := φ.one_of_mem_closedBall (by simpa [mem_closedBall, dist_zero_right] using hy)
      simp [this]
  -- the clamp `σ(s) = max(0, min(s, 1))`
  obtain ⟨σ, hσ, hσb, hσid⟩ : ∃ σ : ℝ → ℝ, LipschitzWith 1 σ ∧ (∀ s, |σ s| ≤ 1) ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, σ s = s := by
    refine ⟨fun s => max 0 (min s 1), (LipschitzWith.id.min_const 1).const_max 0, ?_, ?_⟩
    · intro s
      rw [abs_le]; constructor
      · have : (0 : ℝ) ≤ max 0 (min s 1) := le_max_left _ _
        linarith
      · exact max_le (by norm_num) (min_le_right _ _)
    · intro s hs
      simp only [min_eq_left hs.2.le, max_eq_right hs.1.le]
  -- coordinate maps `π₀ z = z₀`, `π' z = tail z`
  let π0 : Euclid (n + 1) →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hπ0 : ∀ z, π0 z = WithLp.ofLp z 0 := fun z => rfl
  let πtl : Euclid (n + 1) →ₗ[ℝ] Euclid n :=
    { toFun := fun z => WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  let πt : Euclid (n + 1) →L[ℝ] Euclid n := LinearMap.toContinuousLinearMap πtl
  have hπt : ∀ z, πt z = WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) := fun z => rfl
  -- step 2: the map `H(z) = σ(z₀) • r(G(tail z))`
  refine ⟨fun z => σ (WithLp.ofLp z 0) • r (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))), ?_, ?_⟩
  · -- step 3(a): `H` is Lipschitz
    have h1 : LipschitzWith (1 * ‖π0‖₊) (fun z : Euclid (n + 1) => σ (WithLp.ofLp z 0)) :=
      hσ.comp π0.lipschitzWith
    have h2 : LipschitzWith (Kr * (L * ‖πt‖₊))
        (fun z : Euclid (n + 1) => r (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))))) :=
      hKr.comp (hG.comp πt.lipschitzWith)
    refine ⟨_, LipschitzWith.of_dist_le' (K := (ρ' + 1) * ((1 * ‖π0‖₊ : NNReal) : ℝ) +
      ((Kr * (L * ‖πt‖₊) : NNReal) : ℝ)) fun z z' => ?_⟩
    have e1 := h1.dist_le_mul z z'
    have e2 := h2.dist_le_mul z z'
    simp only [dist_eq_norm] at e1 e2 ⊢
    set a := σ (WithLp.ofLp z 0)
    set a' := σ (WithLp.ofLp z' 0)
    set R := r (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))))
    set R' := r (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z'))))
    have ha' : ‖a'‖ ≤ 1 := (Real.norm_eq_abs _).le.trans (hσb _)
    calc ‖a • R - a' • R'‖ = ‖(a - a') • R + a' • (R - R')‖ := by
          congr 1; rw [sub_smul, smul_sub]; abel
      _ ≤ ‖a - a'‖ * ‖R‖ + ‖a'‖ * ‖R - R'‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul (a - a') R, norm_smul a' (R - R')]
      _ ≤ (((1 * ‖π0‖₊ : NNReal) : ℝ) * ‖z - z'‖) * (ρ' + 1) +
            1 * (((Kr * (L * ‖πt‖₊) : NNReal) : ℝ) * ‖z - z'‖) := by
          gcongr
          exact hr_bound _
      _ = ((ρ' + 1) * ((1 * ‖π0‖₊ : NNReal) : ℝ) + ((Kr * (L * ‖πt‖₊) : NNReal) : ℝ)) *
            ‖z - z'‖ := by ring
  · -- step 4: value and derivative on `{z₀ ∈ (0,1), ‖G(tail z)‖ < ρ}`
    intro z hz hzρ
    let Ht : Euclid (n + 1) → Euclid P := fun z' => π0 z' • G (πt z')
    let O : Set (Euclid (n + 1)) := {z' | π0 z' ∈ Ioo (0 : ℝ) 1 ∧ ‖G (πt z')‖ < ρ'}
    have hO : IsOpen O :=
      (isOpen_Ioo.preimage π0.continuous).inter
        (isOpen_lt (continuous_norm.comp (hG.continuous.comp πt.continuous)) continuous_const)
    have hzO : z ∈ O := ⟨hz, lt_of_lt_of_le hzρ (le_max_left _ _)⟩
    have hEq : ∀ z' ∈ O, σ (WithLp.ofLp z' 0) • r (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z')))) =
        Ht z' := by
      rintro z' ⟨h0, hρz⟩
      rw [hπ0] at h0
      rw [hπt] at hρz
      show _ = π0 z' • G (πt z')
      rw [hπ0, hπt, hσid _ h0, hr_id _ hρz.le]
    have hev : (fun z' : Euclid (n + 1) =>
        σ (WithLp.ofLp z' 0) • r (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z'))))) =ᶠ[𝓝 z] Ht :=
      Filter.eventuallyEq_of_mem (hO.mem_nhds hzO) hEq
    refine ⟨hEq z hzO, fun hGd => ?_⟩
    have hD : HasFDerivAt Ht (π0 z • (fderiv ℝ G (πt z)).comp πt + π0.smulRight (G (πt z))) z :=
      π0.hasFDerivAt.smul (hGd.hasFDerivAt.comp z πt.hasFDerivAt)
    rw [hev.fderiv_eq, hD.fderiv]
    have hs0 : π0 (EuclideanSpace.single 0 1) = 1 := by simp [π0]
    have hss : ∀ a : Fin n, π0 (EuclideanSpace.single a.succ 1) = 0 := by
      intro a; simp [π0, Fin.succ_ne_zero]
    have ht0 : πt (EuclideanSpace.single 0 1) = 0 := by
      rw [hπt]; ext j; simp [Fin.tail, Fin.succ_ne_zero]
    have hts : ∀ a : Fin n, πt (EuclideanSpace.single a.succ 1) = EuclideanSpace.single a 1 := by
      intro a; rw [hπt]; ext j; simp [Fin.tail]
    funext b
    refine Fin.cases ?_ (fun a => ?_) b
    · simp [hs0, ht0]
      rfl
    · simp [hss, hts]
      rfl

## Key steps

1. ρ′ := max(ρ, 1). Let r(y) := φ(y)·y, with φ the ContDiffBump with radii ρ′ < ρ′ + 1. Then r is Lipschitz (C¹ with compact support), ‖r‖ ≤ ρ′ + 1 and r = id on closedBall(0, ρ′). The clamp σ(s) := max(0, min(s, 1)) is 1-Lipschitz, |σ| ≤ 1 and σ = id on (0, 1).
2. H(z) := σ(z_0)·r(G(tail z)) is Lipschitz, by the product estimate using the bounds on σ and r and the Lipschitz coordinate maps.
3. On the open set O = {z′ : z′_0 ∈ (0, 1), ‖G(tail z′)‖ < ρ′} ∋ z, H coincides with H̃(z′) := z′_0·G(tail z′), so H(z) = z_0·G(tail z).
4. By the product and chain rules and EventuallyEq.fderiv_eq, DH(z)v = z_0·DG(u)(tail v) + v_0·G(u). Evaluating at ê_0 and ê_{a+1} gives Fin.cons (G(u)) (a ↦ z_0·DG(u)e_a).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (b4d606d, 25730c7c, 2b36630: pins match)`
- `cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (both identical)`
- `python3 over dag.json: depth histogram (depth-6 nodes have no children; the selected node has depth 5); keyword search of lean_statements for Fin.tail|Fin.cons|piFinSuccAbove|Ioo 0 1|curryLeft|ofLp|toLp|volume_preserving|MeasurePreserving|EuclideanSpace.single 0`
- `python3 over dag.json: search for retract|ContDiffBump|closedBall 0 together with LipschitzWith (no reusable Lipschitz retraction); search of lean_name/id for cone (ecf_cone_parametrization and ecf_cone_current are decomposing, with different types)`
- `python3 over dag.json: statements, statuses and candidate commits of cmcdt_lpi_cyl_fubini, cmcdt_lpi_cyl_pullback_integrable, cmcdt_lp_covector_curryLeft_norm_le, cmcdt_lpi_cyl_piece_action, cmcdt_lpi_cyl_piece_mass, cmcdt_lpi_cyl_slice_covector_bound, cmcdt_lpi_cyl_suspension_map, dimred_mbl_dt_lp_imc_cylinder_measure, dor_lmb_fcdp_homotopy_maps`
- `git show 8597f3f / ed778d4 / 0ea228e :GMT/Ch07/Submission.lean | grep ^import (no added imports), and extraction of the accepted proofs between the contract's end and main_theorem`
- `rg dimred_cs_sos_cfs_ over nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-* and dag.json (dimred_cs_sos_cfs_cp_* unused)`
- `grep -n 'homotopy\|cone' book/chapter-06.txt (2.25–2.27 at lines 441–478; 2.30 at lines 525–536)`
- `grep SimonGMT Chapter06/Forms.lean, Currents.lean, Mass.lean for Covector, DifferentialForm, IsSmoothForm, IsTestForm, testFormOnSubmodule, TestFormOn, covectorEuclideanNorm`
- `rg in the Mathlib snapshot for ContDiff.lipschitzWith_of_hasCompactSupport, one_of_mem_closedBall, zero_of_le_dist, curryLeft_apply_apply, curryLeftLI, ContinuousAlternatingMap.apply, map_smul_univ, intervalIntegral_comp_comm, integral_Ioc_eq_integral_Ioo, measurable_fderiv_apply_const, norm_fderiv_le_of_lipschitz, of_dist_le', HasFDerivAt.smul, EventuallyEq.fderiv_eq, setLIntegral_mono, setIntegral_congr_fun, measurable_of_countable`
- `lake env lean /tmp/cp-decomp/Probe.lean (#check of the cited APIs; LipschitzWith.smul does not exist)`
- `lake env lean /tmp/cp-decomp/Check1.lean (six child stubs plus the parent assembly)`
- `lake env lean /tmp/cp-decomp/ConeMap.lean, /tmp/cp-decomp/PieceBounds.lean, /tmp/cp-decomp/PieceAction.lean (new children fully proved)`
- `lake env lean /tmp/cp-decomp/Full.lean (accepted reuse proofs from the three commits, the three new child proofs and the assembly; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-292ca82b13/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-2cc8704e5d/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-36d21f0b90/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-c728da6cee/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-14afd577b6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/tmp/cp-decomp/Probe.lean`
- `/tmp/cp-decomp/Check1.lean`
- `/tmp/cp-decomp/ConeMap.lean`
- `/tmp/cp-decomp/PieceBounds.lean`
- `/tmp/cp-decomp/PieceAction.lean`
- `/tmp/cp-decomp/Full.lean`

Pins and contract. The project (b4d606d), Mathlib (25730c7c) and SimonGMT (2b36630) pins match the manifest. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

DAG. The selected node has depth 5, and depth-6 nodes have no children. The three new children are therefore leaves, and each one was proved in Lean here.

Reuse. The DAG already has accepted, compatible lemmas for the generic parts:
- cmcdt_lpi_cyl_fubini (8597f3f): the cylinder B is Borel, with Tonelli and Fubini in the coordinates ι(t, u);
- cmcdt_lpi_cyl_pullback_integrable (ed778d4): an integrable weight times a Lipschitz pull-back of a test form is integrable;
- cmcdt_lp_covector_curryLeft_norm_le (0ea228e): |ι_vβ| ≤ ‖v‖|β|.
Their frozen types were copied byte-for-byte from dag.json and match their handoffs. Their commits add no imports.

No match for the cone-specific parts. The DAG has no reusable cone map, Lipschitz retraction or cone change of variables:
- cmcdt_lpi_cyl_suspension_map, cmcdt_lpi_cyl_piece_action and cmcdt_lpi_cyl_piece_mass concern the cylinder map (t, u) ↦ (t, G u), not s·G(u);
- ecf_cone_parametrization and ecf_cone_current are still decomposing and use Jacobian weights.

Library. SimonGMT supplies TestFormOn (smooth with compact support, via testFormOnSubmodule), Covector, DifferentialForm and covectorEuclideanNorm. Every Mathlib API cited by the children exists in the snapshot and was probed with #check. LipschitzWith.smul does not exist, so cone_map proves the product estimate directly.

Lean. Check1, the three child files and Full.lean compile. The frozen parent type is proved from the six children, and the full chain uses only propext, Classical.choice and Quot.sound.

Book. The construction is Simon Ch. 6, 2.30: the cone 0 ⨯ T = h_#([[(0,1)]] × T) with h(t, x) = tx (chapter-06.txt lines 525–536), together with the integral formula from the proof of 2.27 (lines 468–476).
