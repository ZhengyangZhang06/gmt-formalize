# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1.grad_norm_sq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the notation paragraph of the parent proof, isolated as a lemma: the operator norm ‖Du(y)‖ is the Euclidean length of the gradient, and by Cauchy–Schwarz |∇u·Φ| ≤ ‖Du‖·|Φ|. It also gives the identity ∇h·Φ = χ_r‖Dh‖² of parent step 4. Both the duality-bound child and the interior-energy child use it.

1. (Riesz representative.) Let g := (InnerProductSpace.toDual ℝ ℝⁿ).symm L ∈ ℝⁿ. Since toDual is a linear isometric equivalence ℝⁿ ≃ (ℝⁿ)*, we have ⟪g, v⟫ = L v for every v ∈ ℝⁿ (InnerProductSpace.toDual_symm_apply) and ‖g‖ = ‖L‖.
2. (Coordinates.) For each i, L(e_i) = ⟪g, e_i⟫ = ⟪e_i, g⟫ = g_i. This uses symmetry of the real inner product (real_inner_comm) and EuclideanSpace.inner_single_left, which gives ⟪single i 1, v⟫ = 1·v_i.
3. (Part (i).) ‖L‖² = ‖g‖² = Σ_i g_i², by EuclideanSpace.real_norm_sq_eq. By step 2 this equals Σ_i L(e_i)².
4. (Norm as a square root.) Since ‖L‖ ≥ 0, part (i) gives ‖L‖ = √(Σ_i L(e_i)²) (Real.sqrt_sq).
5. (Part (ii).) The finite Cauchy–Schwarz inequality (Real.sum_mul_le_sqrt_mul_sqrt) says that Σ_i x_i y_i ≤ √(Σ_i x_i²)·√(Σ_i y_i²) for x, y : Fin n → ℝ.
   - With x_i = L(e_i) and y_i = a_i, step 4 gives Σ_i L(e_i)a_i ≤ ‖L‖·√(Σ_i a_i²).
   - With y_i = −a_i, and using (−a_i)² = a_i², it gives −Σ_i L(e_i)a_i ≤ ‖L‖·√(Σ_i a_i²).
   - Together these give |Σ_i L(e_i)a_i| ≤ ‖L‖·√(Σ_i a_i²) (abs_le). ∎
For n = 0 every sum is empty and L = 0, so (i) and (ii) read 0 = 0 and 0 ≤ 0. The argument covers this case without change.

Appendix (Lean proof, kernel-checked). This proof was compiled against the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c). It was placed inside `namespace GMT.Ch07` -> `namespace Submission` of a copy of GMT/Ch07/Submission.lean at b4d606d, after the `noncomputable section ... end` block and before `main_theorem`. The contract's `open`s are in scope there. `#print axioms` gives only propext, Classical.choice and Quot.sound. Sibling children are referenced by their bare names.

theorem dorag_ha_lsc_grad_norm_sq : ∀ (n : ℕ) (L : Euclid n →L[ℝ] ℝ), ‖L‖ ^ 2 = ∑ i : Fin n, L (EuclideanSpace.single i (1 : ℝ)) ^ 2 ∧ ∀ a : Fin n → ℝ, |∑ i : Fin n, L (EuclideanSpace.single i (1 : ℝ)) * a i| ≤ ‖L‖ * Real.sqrt (∑ i : Fin n, a i ^ 2) := by
  intro n L
  set g : Euclid n := (InnerProductSpace.toDual ℝ (Euclid n)).symm L with hg
  have hgL : ∀ v, inner ℝ g v = L v := fun v => InnerProductSpace.toDual_symm_apply
  have hnorm : ‖g‖ = ‖L‖ := by simp [hg]
  have hcoord : ∀ i, L (EuclideanSpace.single i (1 : ℝ)) = g i := by
    intro i
    rw [← hgL, real_inner_comm, EuclideanSpace.inner_single_left]; simp
  have hid : ‖L‖ ^ 2 = ∑ i : Fin n, L (EuclideanSpace.single i (1 : ℝ)) ^ 2 := by
    rw [← hnorm, EuclideanSpace.real_norm_sq_eq]; simp_rw [hcoord]
  refine ⟨hid, fun a => ?_⟩
  have hL : ‖L‖ = Real.sqrt (∑ i, L (EuclideanSpace.single i (1:ℝ)) ^ 2) := by
    rw [← hid, Real.sqrt_sq (norm_nonneg _)]
  rw [hL, abs_le]
  constructor
  · have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => L (EuclideanSpace.single i (1:ℝ))) (fun i => -a i)
    simp only [neg_sq, mul_neg, Finset.sum_neg_distrib] at this
    linarith
  · exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

## Key steps

1. Represent L by g := toDual⁻¹(L) ∈ ℝⁿ: ⟪g, v⟫ = L v, ‖g‖ = ‖L‖, and g_i = L(e_i).
2. ‖L‖² = ‖g‖² = Σ_i g_i² = Σ_i L(e_i)².
3. ‖L‖ = √(Σ_i L(e_i)²); finite Cauchy–Schwarz applied to a and to −a gives |Σ_i L(e_i)a_i| ≤ ‖L‖·√(Σ_i a_i²).

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
