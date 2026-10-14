# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_param-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_param-a1.piece_action-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 8(a)–(c) of the selected parent proof, for one piece. It is the parametrized form of the cone formula behind Simon Ch. 6, 2.30 (chapter-06.txt lines 525–536). With h(t, x) = tx, the computation in the proof of 2.27 (lines 468–476) reads h_#([[(0,1)]] × T)(ω) = ∫_0^1 ∫ ⟨ω(tx), x ∧ t^n T⃗(x)⟩ dμ_T(x) dt. Uses the siblings cyl_fubini (the accepted cmcdt_lpi_cyl_fubini) and pullback_integrable (the accepted cmcdt_lpi_cyl_pullback_integrable).
Notation. ι(t, u) := WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) ∈ ℝ^{n+1}, so that ι(t, u)_0 = t and tail ι(t, u) = u. DG(u)e := (a ↦ DG(u)e_a) and DH(z)ê := (b ↦ DH(z)ê_b). h(z) := w(tail z), and F(z) := h(z)·ω(H z)(DH(z)ê).

1. (h is integrable on B.) h is measurable (w is measurable as a map out of ℤ, and tail is continuous). By cyl_fubini (b) with f = ‖h‖ₑ, ∫⁻_B ‖h‖ₑ = ∫⁻_A ∫⁻_{(0,1)} ‖w(u)‖ₑ dt du = ∫⁻_A ‖w(u)‖ₑ du < ∞, using vol((0, 1)) = 1 and the integrability of w on A. So h is integrable on B.
2. (F is integrable on B.) Apply pullback_integrable with Q := P, n := n+1, the L-Lipschitz map H, S := B, g := h and the test form ω. It shows that z ↦ h(z)·ω(H z)(DH(z)ê), which is F, is integrable on B.
3. (Fubini.) By step 2 and cyl_fubini (c), ∫_B F = ∫_{u ∈ A} ∫_{t ∈ (0,1)} F(ι(t, u)) dt du. Since A is measurable, it suffices (setIntegral_congr_fun) to prove for every u ∈ A that
 w(u)·η(G u)(DG(u)e) = ∫_{(0,1)} F(ι(t, u)) dt.   (†)
 Fix u ∈ A and write v := G(u) and x := DG(u)e ∈ (ℝ^P)^n.
4. (Inner integrand.) Let t ∈ (0, 1) and z := ι(t, u). Then z_0 = t ∈ (0, 1) and tail z = u ∈ A, so z ∈ B. By (H1), H(z) = t·v and DH(z)ê = Fin.cons v (a ↦ t·x_a). For every (n+1)-covector α, α(Fin.cons v (a ↦ t·x_a)) = (α.curryLeft v)(a ↦ t·x_a) = t^n·(α.curryLeft v)(x) = t^n·α(Fin.cons v x). This uses curryLeft_apply_apply, with Matrix.vecCons = Fin.cons, and multilinearity (map_smul_univ, ∏_{a ∈ Fin n} t = t^n). Hence
 F(ι(t, u)) = w(u)·ω(t·v)(Fin.cons v (a ↦ t·x_a)) = w(u)·(t^n·ω(t·v)(Fin.cons v x)).
 Integrating over (0, 1) (setIntegral_congr_fun on the measurable (0, 1), then integral_const_mul) gives ∫_{(0,1)} F(ι(t, u)) dt = w(u)·∫_{(0,1)} t^n·ω(t·v)(Fin.cons v x) dt.
5. (The homotopy integral.) By (H2), η(v) = ∫_0^1 k(t) dt with k(t) := t^n·(ω(t·v)).curryLeft v. k is continuous. Indeed t ↦ ω(t·v) is continuous (ω is smooth), and β ↦ β.curryLeft v is continuous linear, being β ↦ (curryLeftLI β)(v) for the linear isometry curryLeftLI. So k is interval integrable on [0, 1]. Evaluation at the fixed tuple x, E_x(β) := β(x), is a continuous linear functional on n-covectors (ContinuousAlternatingMap.apply). Hence, by ContinuousLinearMap.intervalIntegral_comp_comm,
 η(v)(x) = E_x(∫_0^1 k) = ∫_0^1 E_x(k(t)) dt = ∫_0^1 t^n·((ω(t·v)).curryLeft v)(x) dt = ∫_0^1 t^n·ω(t·v)(Fin.cons v x) dt,
 again by curryLeft_apply_apply. Since 0 ≤ 1, the interval integral equals the integral over (0, 1] (intervalIntegral.integral_of_le), which equals the integral over (0, 1) because single points are null (integral_Ioc_eq_integral_Ioo).
6. (Conclusion.) Steps 4 and 5 give (†): w(u)·η(G u)(DG(u)e) = w(u)·∫_{(0,1)} t^n·ω(t·v)(Fin.cons v x) dt = ∫_{(0,1)} F(ι(t, u)) dt. With step 3, ∫_A w(u)·η(G u)(DG(u)e) du = ∫_A ∫_{(0,1)} F(ι(t, u)) dt du = ∫_B F, which is the claim. ∎

Appendix (supplementary; the numbered argument above is complete without it). The following Lean proof of exactly this frozen statement was checked during decomposition with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c) after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's opens, with the declaration named Submission.dimred_cs_sos_cfs_cp_piece_action as in accepted nodes. It references the siblings Submission.cmcdt_lpi_cyl_fubini and Submission.cmcdt_lpi_cyl_pullback_integrable, and it was compiled both against stubs of them and together with their accepted proofs from the candidate commits 8597f3f and ed778d4. Its axioms are propext, Classical.choice and Quot.sound only.
Lean tactic block for `theorem Submission.dimred_cs_sos_cfs_cp_piece_action`, whose type is exactly the frozen lean_statement of this child (it follows `:= by`):
  intro P n L G H A w ω η hHL hA hw hwi hHB hη
  obtain ⟨hBm, hlin, hfub⟩ := Submission.cmcdt_lpi_cyl_fubini n A hA
  have htail : Measurable (fun z : Euclid (n + 1) =>
      (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n)) := by
    fun_prop
  have hιtail : ∀ (t : ℝ) (u : Euclid n),
      (WithLp.toLp 2 (Fin.tail (WithLp.ofLp
        (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (n + 1)))) : Euclid n) = u := by
    intro t u; simp
  have hι0 : ∀ (t : ℝ) (u : Euclid n),
      WithLp.ofLp (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (n + 1)) 0 = t := by
    intro t u; simp
  have hwR : Measurable (fun u => (w u : ℝ)) := (measurable_of_countable _).comp hw
  -- `h = w ∘ tail` is integrable on `B`
  have hint : IntegrableOn (fun z : Euclid (n + 1) => (w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) : ℝ))
      {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧
        (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A} := by
    refine ⟨(hwR.comp htail).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hlin (fun z => ‖(w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) : ℝ)‖ₑ)
      (hwR.comp htail).enorm]
    simp only [hιtail]
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]
    exact hwi.2
  -- the integrand on `B` is integrable (accepted pullback lemma), so Fubini applies
  have hF := Submission.cmcdt_lpi_cyl_pullback_integrable P (n + 1) L H _ _ ω hHL hint
  rw [hfub _ hF]
  refine setIntegral_congr_fun hA fun u hu => ?_
  have hωc : Continuous (ω : DifferentialForm (Euclid P) (n + 1)) := ω.2.1.1.continuous
  -- the covector identity `α(x, s v) = sⁿ α(x, v)`
  have hsc : ∀ (α : Covector (Euclid P) (n + 1)) (x : Euclid P) (v : Fin n → Euclid P) (s : ℝ),
      α (Fin.cons x (fun a => s • v a)) = s ^ n * α (Fin.cons x v) := by
    intro α x v s
    have h1 : α (Fin.cons x (fun a => s • v a)) = (α.curryLeft x) (fun a => s • v a) := rfl
    have h2 : α (Fin.cons x v) = (α.curryLeft x) v := rfl
    rw [h1, h2, ContinuousAlternatingMap.map_smul_univ (α.curryLeft x) (fun _ => s)]
    simp
  -- the inner integrand on `(0, 1)`
  have hinner : ∀ t ∈ Ioo (0 : ℝ) 1,
      (w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp
          (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (n + 1))))) : ℝ) *
        (ω : DifferentialForm (Euclid P) (n + 1)) (H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))))
          (fun b => fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) (EuclideanSpace.single b 1)) =
      (w u : ℝ) * (t ^ n * (ω : DifferentialForm (Euclid P) (n + 1)) (t • G u)
        (Fin.cons (G u) (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)))) := by
    intro t ht
    have hz : WithLp.ofLp (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (n + 1)) 0 ∈
        Ioo (0 : ℝ) 1 := by rw [hι0]; exact ht
    have hzA : (WithLp.toLp 2 (Fin.tail (WithLp.ofLp
        (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (n + 1)))) : Euclid n) ∈ A := by
      rw [hιtail]; exact hu
    obtain ⟨h1, h2⟩ := hHB _ hz hzA
    rw [h1, h2]
    simp only [hιtail, Fin.cons_zero]
    rw [hsc]
  rw [setIntegral_congr_fun measurableSet_Ioo hinner, integral_const_mul]
  congr 1
  rw [hη u hu]
  have hcont : Continuous (fun t : ℝ =>
      t ^ n • ((ω : DifferentialForm (Euclid P) (n + 1)) (t • G u)).curryLeft (G u)) := by
    have : Continuous (fun t : ℝ => (ω : DifferentialForm (Euclid P) (n + 1)) (t • G u)) :=
      hωc.comp (continuous_id.smul continuous_const)
    exact (continuous_pow n).smul
      ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Euclid P) (F := ℝ) (n := n)).continuous.comp
        this |>.clm_apply continuous_const)
  have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm
    (ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)))
    (hcont.intervalIntegrable (μ := volume) 0 1)
  rw [← ContinuousAlternatingMap.apply_apply, ← hcomm,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  simp only [ContinuousAlternatingMap.apply_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rfl

## Key steps

1. w∘tail is integrable on B (Tonelli via cyl_fubini), so F = (w∘tail)·ω(H)(DH ê) is integrable on B by pullback_integrable, because H is Lipschitz.
2. By Fubini (cyl_fubini (c)), ∫_B F = ∫_A ∫_{(0,1)} F(ι(t, u)) dt du, which reduces the claim to a pointwise identity for u ∈ A.
3. For t ∈ (0, 1): F(ι(t, u)) = w(u)·t^n·ω(t·G u)(Fin.cons (G u) (DG(u)e)), by (H1) and α(Fin.cons v (t·x)) = t^n·α(Fin.cons v x).
4. η(G u)(DG(u)e) = ∫_0^1 t^n·ω(t·G u)(Fin.cons (G u) (DG(u)e)) dt, by evaluating the covector-valued interval integral (intervalIntegral_comp_comm); and ∫_0^1 equals the integral over (0, 1).

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
