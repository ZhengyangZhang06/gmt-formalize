# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1.exhaustion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is step 5 of the parent proof (exhaustion), stated for a general nonnegative integrand that is continuous on B. The parent applies it to f = ‖Dh‖².

1. (Interior integrability.) Let 0 < r < R. Then closedBall(0, r) is compact and contained in B, and f is continuous on it. So f is integrable on closedBall(0, r) (ContinuousOn.integrableOn_compact), and hence on B̆_r(0) ⊆ closedBall(0, r). Also, for every r ≤ R, f ≥ 0 a.e. for Lebesgue measure restricted to B̆_r(0), because B̆_r(0) ⊆ B.
2. (E ≥ 0.) Take r = R/2: 0 ≤ ∫_{B̆_{R/2}(0)} f ≤ E (setIntegral_nonneg).
3. (Lower integrals on interior balls.) For 0 < r < R, step 1 gives ∫⁻_{B̆_r(0)} ofReal(f) = ofReal(∫_{B̆_r(0)} f) ≤ ofReal(E) (ofReal_integral_eq_lintegral_ofReal, ENNReal.ofReal_le_ofReal).
4. (Exhausting radii.) Let r_k := R·(k + 1)/(k + 2) for k ∈ ℕ. Then 0 < r_k < R and k ↦ r_k is nondecreasing. Moreover ⋃_k B̆_{r_k}(0) = B:
   - '⊆' holds since r_k < R;
   - '⊇': given ‖x‖ < R, pick k ∈ ℕ with k > R/(R − ‖x‖) (exists_nat_gt). Then (k + 2)(R − ‖x‖) > R, i.e. ‖x‖ < R(k + 1)/(k + 2) = r_k.
   The parent's r_k = R(1 − 1/(k + 1)) has r_0 = 0; here the index is shifted so that every r_k > 0, as the hypothesis requires.
5. (Monotone convergence.) The balls B̆_{r_k}(0) increase, so they form a directed family. setLIntegral_iUnion_of_directed and step 3 give
   ∫⁻_B ofReal(f) = sup_k ∫⁻_{B̆_{r_k}(0)} ofReal(f) ≤ ofReal(E) < ∞.
6. (Integrability on B.) f is a.e.-strongly measurable for Lebesgue measure restricted to B (ContinuousOn.aestronglyMeasurable, B measurable). Since f ≥ 0 a.e. on B, finite integral is equivalent to ∫⁻_B ofReal(f) < ∞ (hasFiniteIntegral_iff_ofReal), which holds by step 5. Hence f is integrable on B.
7. (The bound.) ofReal(∫_B f) = ∫⁻_B ofReal(f) ≤ ofReal(E), by ofReal_integral_eq_lintegral_ofReal and step 5. Since E ≥ 0 (step 2), this gives ∫_B f ≤ E (ENNReal.ofReal_le_ofReal_iff). ∎

Appendix (Lean proof, kernel-checked). This proof was compiled against the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c). It was placed inside `namespace GMT.Ch07` -> `namespace Submission` of a copy of GMT/Ch07/Submission.lean at b4d606d, after the `noncomputable section ... end` block and before `main_theorem`. The contract's `open`s are in scope there. `#print axioms` gives only propext, Classical.choice and Quot.sound. Sibling children are referenced by their bare names.

theorem dorag_ha_lsc_exhaustion : ∀ (n : ℕ) (R E : ℝ) (f : Euclid n → ℝ), 0 < R → ContinuousOn f (ball (0 : Euclid n) R) → (∀ x ∈ ball (0 : Euclid n) R, 0 ≤ f x) → (∀ r, 0 < r → r < R → ∫ x in ball (0 : Euclid n) r, f x ≤ E) → IntegrableOn f (ball (0 : Euclid n) R) ∧ ∫ x in ball (0 : Euclid n) R, f x ≤ E := by
  intro n R E f hR hf hf0 hbd
  -- integrability on interior balls
  have hint : ∀ r, 0 < r → r < R → IntegrableOn f (ball (0 : Euclid n) r) := by
    intro r _ hrR
    exact ((hf.mono (closedBall_subset_ball hrR)).integrableOn_compact
      (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  have hnn : ∀ r, r ≤ R → 0 ≤ᵐ[volume.restrict (ball (0 : Euclid n) r)] f := by
    intro r hrR
    exact (ae_restrict_iff' measurableSet_ball).2
      (Eventually.of_forall fun x hx => hf0 x (ball_subset_ball hrR hx))
  have hE0 : 0 ≤ E := (setIntegral_nonneg measurableSet_ball fun x hx =>
      hf0 x (ball_subset_ball (half_le_self hR.le) hx)).trans (hbd (R / 2) (half_pos hR) (half_lt_self hR))
  -- exhausting sequence of radii
  set r : ℕ → ℝ := fun k => R * ((k + 1) / (k + 2)) with hr
  have hr_pos : ∀ k, 0 < r k := fun k => by positivity
  have hr_lt : ∀ k, r k < R := fun k => by
    have : ((k:ℝ) + 1) / (k + 2) < 1 := by rw [div_lt_one (by positivity)]; linarith
    calc r k = R * ((k + 1) / (k + 2)) := rfl
      _ < R * 1 := by gcongr
      _ = R := mul_one R
  have hr_mono : Monotone r := by
    intro k l hkl
    have hkl' : (k:ℝ) ≤ l := by exact_mod_cast hkl
    have hfrac : ((k:ℝ) + 1) / (k + 2) ≤ ((l:ℝ) + 1) / (l + 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    exact mul_le_mul_of_nonneg_left hfrac hR.le
  have hunion : (⋃ k, ball (0 : Euclid n) (r k)) = ball (0 : Euclid n) R := by
    apply Subset.antisymm
    · exact iUnion_subset fun k => ball_subset_ball (hr_lt k).le
    · intro x hx
      rw [mem_ball_zero_iff] at hx
      obtain ⟨k, hk⟩ := exists_nat_gt (R / (R - ‖x‖))
      refine mem_iUnion.2 ⟨k, mem_ball_zero_iff.2 ?_⟩
      have hpos : 0 < R - ‖x‖ := by linarith
      have hk2 : R < (k + 2) * (R - ‖x‖) := by
        rw [div_lt_iff₀ hpos] at hk; nlinarith
      show ‖x‖ < R * ((k + 1) / (k + 2))
      rw [mul_div_assoc', lt_div_iff₀ (by positivity)]
      nlinarith
  have hdir : Directed (· ⊆ ·) fun k => ball (0 : Euclid n) (r k) :=
    Monotone.directed_le fun a b hab => ball_subset_ball (hr_mono hab)
  -- lintegral bound
  have hlin : ∫⁻ x in ball (0 : Euclid n) R, ENNReal.ofReal (f x) ≤ ENNReal.ofReal E := by
    rw [← hunion, setLIntegral_iUnion_of_directed _ hdir]
    refine iSup_le fun k => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hint _ (hr_pos k) (hr_lt k)) (hnn _ (hr_lt k).le)]
    exact ENNReal.ofReal_le_ofReal (hbd _ (hr_pos k) (hr_lt k))
  have hmeas : AEStronglyMeasurable f (volume.restrict (ball (0 : Euclid n) R)) :=
    hf.aestronglyMeasurable measurableSet_ball
  have hI : IntegrableOn f (ball (0 : Euclid n) R) := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (hnn R le_rfl)]
    exact hlin.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hI, ?_⟩
  have := (ofReal_integral_eq_lintegral_ofReal hI (hnn R le_rfl)).trans_le hlin
  exact (ENNReal.ofReal_le_ofReal_iff hE0).1 this

## Key steps

1. f is integrable on each B̆_r(0) with r < R, and ∫⁻ ofReal f = ofReal ∫ f ≤ ofReal E there; also E ≥ 0.
2. r_k := R(k + 1)/(k + 2) increases to R, and ⋃_k B̆_{r_k}(0) = B.
3. Monotone convergence over the directed balls (setLIntegral_iUnion_of_directed): ∫⁻_B ofReal f ≤ ofReal E < ∞.
4. Continuity on B gives measurability, hence integrability on B; convert back to get ∫_B f ≤ E.

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
