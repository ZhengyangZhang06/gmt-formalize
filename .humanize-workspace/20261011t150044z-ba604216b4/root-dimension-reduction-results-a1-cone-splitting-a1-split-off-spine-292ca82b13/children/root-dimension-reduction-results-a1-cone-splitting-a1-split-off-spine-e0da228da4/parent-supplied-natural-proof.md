# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_param-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_param-a1.piece_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 3(c), 5, 6 and 7 of the selected parent proof, for one piece. Uses the siblings cyl_fubini (the accepted cmcdt_lpi_cyl_fubini) and curry_le (the accepted cmcdt_lp_covector_curryLeft_norm_le).
Notation. ι(t, u) := WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) ∈ ℝ^{n+1} for t ∈ ℝ, u ∈ ℝ^n. Then ι(t, u)_0 = t and tail ι(t, u) = u (Fin.cons_zero, Fin.tail_cons, WithLp.ofLp_toLp). For an n-covector β, βDG(u)e denotes β(a ↦ DG(u)e_a).

0. (Preliminaries.) z ↦ z_0 and z ↦ tail z are continuous, hence measurable. u ↦ (w(u) : ℝ) is measurable, since every map out of the countable discrete ℤ is measurable (measurable_of_countable). By cyl_fubini applied to (n, A), B is measurable, and for every measurable f : ℝ^{n+1} → [0, ∞]
 ∫⁻_B f = ∫⁻_{u ∈ A} ∫⁻_{t ∈ (0,1)} f(ι(t, u)) dt du.   (∗)
1. (Part (i).) h := w∘tail is measurable, hence a.e. strongly measurable. Apply (∗) to f(z) := ‖h(z)‖ₑ, so that f(ι(t, u)) = ‖w(u)‖ₑ: ∫⁻_B ‖h‖ₑ = ∫⁻_A ∫⁻_{(0,1)} ‖w(u)‖ₑ dt du = ∫⁻_A ‖w(u)‖ₑ·vol((0, 1)) du = ∫⁻_A ‖w(u)‖ₑ du < ∞. Here vol((0, 1)) = 1 (Real.volume_Ioo), and the last integral is finite because w is integrable on A. So h is integrable on B.
2. (Covector identity.) For an (n+1)-covector α, x ∈ ℝ^P, v ∈ (ℝ^P)^n and s ∈ ℝ:
 α(Fin.cons x (a ↦ s·v_a)) = (α.curryLeft x)(a ↦ s·v_a) = (∏_{a ∈ Fin n} s)·(α.curryLeft x)(v) = s^n·(α.curryLeft x)(v).
 The first equality is ContinuousAlternatingMap.curryLeft_apply_apply (α.curryLeft x v = α(Matrix.vecCons x v), and Matrix.vecCons = Fin.cons definitionally). The second is multilinearity (ContinuousAlternatingMap.map_smul_univ).
3. (Part (ii).) Fix z ∈ B and put s := z_0 ∈ (0, 1), u := tail z ∈ A and v := G(u). Then c′(z) = s^n·‖v‖·c(u) ≥ 0, because s > 0, ‖v‖ ≥ 0 and c(u) ≥ 0. Let α be an (n+1)-covector. By the hypothesis on DH at z ∈ B and step 2,
 α(DH(z)ê) = α(Fin.cons v (a ↦ s·DG(u)e_a)) = s^n·(α.curryLeft v)(DG(u)e).
 Hence, using s^n ≥ 0, then the hypothesis on c at u applied to the n-covector α.curryLeft v, then curry_le (|α.curryLeft v| ≤ ‖v‖·|α|) together with c(u) ≥ 0:
 |α(DH(z)ê)| = s^n·|(α.curryLeft v)(DG(u)e)| ≤ s^n·c(u)·|α.curryLeft v| ≤ s^n·c(u)·‖v‖·|α| = c′(z)·|α|.
4. (Part (iii).) The function f(z) := ofReal(|w(tail z)|·c′(z)) is measurable, as a composition of products of measurable functions (G and c are measurable). By (∗),
 ∫⁻_B f = ∫⁻_{u ∈ A} ∫⁻_{t ∈ (0,1)} ofReal(|w(u)|·(t^n·‖G(u)‖·c(u))) dt du.
 Fix u ∈ A. Then c(u) ≥ 0 and 0 ≤ ‖G(u)‖ ≤ ρ, so in particular ρ ≥ 0. For t ∈ (0, 1) we have 0 ≤ t^n ≤ 1, hence |w(u)|·(t^n·‖G(u)‖·c(u)) ≤ |w(u)|·(1·ρ·c(u)) = ρ·(|w(u)|·c(u)), and ofReal(ρ·x) = ofReal(ρ)·ofReal(x) because ρ ≥ 0 (ENNReal.ofReal_mul). Therefore the inner integral is at most ∫⁻_{(0,1)} ofReal(ρ)·ofReal(|w(u)|·c(u)) dt = ofReal(ρ)·ofReal(|w(u)|·c(u))·vol((0, 1)) = ofReal(ρ)·ofReal(|w(u)|·c(u)) (setLIntegral_mono, setLIntegral_const).
 Integrating over A (setLIntegral_mono, the right side being measurable) and pulling out the constant (lintegral_const_mul) gives
 ∫⁻_B f ≤ ∫⁻_A ofReal(ρ)·ofReal(|w(u)|·c(u)) du = ofReal(ρ)·∫⁻_A ofReal(|w(u)|·c(u)) du.
 (If A = ∅ both sides vanish; the inequality ρ ≥ 0 is only used at points u ∈ A.) ∎

Appendix (supplementary; the numbered argument above is complete without it). The following Lean proof of exactly this frozen statement was checked during decomposition with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c) after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's opens, with the declaration named Submission.dimred_cs_sos_cfs_cp_piece_bounds as in accepted nodes. It references the siblings Submission.cmcdt_lpi_cyl_fubini and Submission.cmcdt_lp_covector_curryLeft_norm_le, and it was compiled both against stubs of them and together with their accepted proofs from the candidate commits 8597f3f and 0ea228e. Its axioms are propext, Classical.choice and Quot.sound only.
Lean tactic block for `theorem Submission.dimred_cs_sos_cfs_cp_piece_bounds`, whose type is exactly the frozen lean_statement of this child (it follows `:= by`):
  intro P n ρ G H A w c hGm hA hw hc hwi hGρ hcb hDH
  obtain ⟨hBm, hlin, -⟩ := Submission.cmcdt_lpi_cyl_fubini n A hA
  have htail : Measurable (fun z : Euclid (n + 1) =>
      (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n)) := by
    fun_prop
  have hz0 : Measurable (fun z : Euclid (n + 1) => WithLp.ofLp z 0) := by
    fun_prop
  have hιtail : ∀ (t : ℝ) (u : Euclid n),
      (WithLp.toLp 2 (Fin.tail (WithLp.ofLp
        (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (n + 1)))) : Euclid n) = u := by
    intro t u; simp
  have hwR : Measurable (fun u => (w u : ℝ)) := (measurable_of_countable _).comp hw
  refine ⟨?_, ?_, ?_⟩
  · -- integrability of `h = w ∘ tail` on `B`
    refine ⟨(hwR.comp htail).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hlin (fun z => ‖(w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) : ℝ)‖ₑ)
      (hwR.comp htail).enorm]
    simp only [hιtail]
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]
    exact hwi.2
  · -- the covector bound
    intro z hz hzA
    set s := WithLp.ofLp z 0
    set u := (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n)
    have hs : 0 < s := hz.1
    obtain ⟨hc0, hcα⟩ := hcb u hzA
    refine ⟨by positivity, fun α => ?_⟩
    rw [hDH z hz hzA]
    have key : α (Fin.cons (G u) (fun a => s • fderiv ℝ G u (EuclideanSpace.single a 1))) =
        s ^ n * (α.curryLeft (G u)) (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) := by
      have h1 : α (Fin.cons (G u) (fun a => s • fderiv ℝ G u (EuclideanSpace.single a 1))) =
          (α.curryLeft (G u)) (fun a => s • fderiv ℝ G u (EuclideanSpace.single a 1)) := rfl
      rw [h1, ContinuousAlternatingMap.map_smul_univ (α.curryLeft (G u)) (fun _ => s)]
      simp
    rw [key, abs_mul, abs_of_nonneg (by positivity)]
    calc s ^ n * |(α.curryLeft (G u)) (fun a => fderiv ℝ G u (EuclideanSpace.single a 1))|
        ≤ s ^ n * (c u * covectorEuclideanNorm (α.curryLeft (G u))) := by
          gcongr; exact hcα _
      _ ≤ s ^ n * (c u * (‖G u‖ * covectorEuclideanNorm α)) := by
          gcongr
          exact Submission.cmcdt_lp_covector_curryLeft_norm_le P n (G u) α
      _ = s ^ n * ‖G u‖ * c u * covectorEuclideanNorm α := by ring
  · -- the mass bound
    have hfm : Measurable (fun z : Euclid (n + 1) =>
        ENNReal.ofReal (|(w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) : ℝ)| *
          (WithLp.ofLp z 0 ^ n * ‖G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))‖ *
            c (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))))) := by
      refine ENNReal.measurable_ofReal.comp ?_
      exact (continuous_abs.measurable.comp (hwR.comp htail)).mul
        (((hz0.pow_const n).mul (hGm.comp htail).norm).mul (hc.comp htail))
    rw [hlin _ hfm]
    simp only [hιtail]
    calc ∫⁻ u in A, ∫⁻ t in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (|(w u : ℝ)| * (t ^ n * ‖G u‖ * c u))
        ≤ ∫⁻ u in A, ENNReal.ofReal ρ * ENNReal.ofReal (|(w u : ℝ)| * c u) := by
          refine setLIntegral_mono (by fun_prop) fun u hu => ?_
          obtain ⟨hc0, -⟩ := hcb u hu
          have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (hGρ u hu)
          calc ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (|(w u : ℝ)| * (t ^ n * ‖G u‖ * c u))
              ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal ρ * ENNReal.ofReal (|(w u : ℝ)| * c u) := by
                refine setLIntegral_mono (by fun_prop) fun t ht => ?_
                rw [← ENNReal.ofReal_mul hρ0]
                refine ENNReal.ofReal_le_ofReal ?_
                have ht1 : t ^ n ≤ 1 := pow_le_one₀ ht.1.le ht.2.le
                have ht0 : 0 ≤ t ^ n := pow_nonneg ht.1.le n
                calc |(w u : ℝ)| * (t ^ n * ‖G u‖ * c u)
                    ≤ |(w u : ℝ)| * (1 * ρ * c u) := by
                      gcongr
                      · exact hGρ u hu
                  _ = ρ * (|(w u : ℝ)| * c u) := by ring
            _ = ENNReal.ofReal ρ * ENNReal.ofReal (|(w u : ℝ)| * c u) := by
                rw [setLIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]
      _ = ENNReal.ofReal ρ * ∫⁻ u in A, ENNReal.ofReal (|(w u : ℝ)| * c u) := by
          rw [lintegral_const_mul]
          fun_prop

## Key steps

1. cyl_fubini: B is Borel and ∫⁻_B f = ∫⁻_A ∫⁻_{(0,1)} f(ι(t, u)) dt du. With f = ‖w∘tail‖ₑ this gives ∫⁻_B |w∘tail| = ∫⁻_A |w| < ∞, so w∘tail is integrable on B.
2. α(Fin.cons v (a ↦ s·x_a)) = s^n·(α.curryLeft v)(x), by curryLeft_apply_apply and map_smul_univ.
3. For z ∈ B, with s = z_0 and u = tail z: |α(DH(z)ê)| = s^n·|(α.curryLeft (G u))(DG(u)e)| ≤ s^n·c(u)·|α.curryLeft (G u)| ≤ s^n·c(u)·‖G u‖·|α| = c′(z)·|α|, by the c-bound and then curry_le.
4. Tonelli via cyl_fubini, with t^n ≤ 1, ‖G u‖ ≤ ρ and vol((0, 1)) = 1, gives ∫⁻_B |w∘tail|·c′ ≤ ofReal(ρ)·∫⁻_A |w|·c.

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
