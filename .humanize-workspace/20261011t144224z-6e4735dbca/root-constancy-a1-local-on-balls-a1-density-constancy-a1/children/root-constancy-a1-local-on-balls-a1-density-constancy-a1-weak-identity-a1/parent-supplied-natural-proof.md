# Parent-supplied natural-language proof

- Parent DAG node: `root.constancy-a1.local_on_balls-a1.density_constancy-a1`
- Child DAG node: `root.constancy-a1.local_on_balls-a1.density_constancy-a1.weak_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon, Introduction to Geometric Measure Theory, Ch. 6, Theorem 2.34 (Constancy Theorem), printed proof pp. 142–143, display (2): “∫ D_j a θ_ε dLⁿ = T(dω_j) = ∂T(ω_j) = 0, j = 1,…,n”. This child is Steps 1–4 of the accepted proof of the parent node root.constancy-a1.local_on_balls-a1.density_constancy-a1, specialized to C^∞ test functions. The hypothesis u(D_j a) = 0 plays the role of T(dω_j) = ∂T(ω_j) = 0, and the kernel φ plays the role of ϕ_ε. [Printed form: with ω_j = (−1)^{j−1} a_ε dx¹∧⋯∧dx^{j−1}∧dx^{j+1}∧⋯∧dxⁿ one has dω_j = (D_j a)_ε dx¹∧⋯∧dxⁿ, where a_ε = ϕ_ε ∗ a.]

Notation.
- ℝⁿ = Eucl n = EuclideanSpace ℝ (Fin n); Lⁿ = Lebesgue measure (Lean: volume).
- spt g = tsupport g; B_s(x) = ball x s; B̄_s(x) = closedBall x s.
- e_j = EuclideanSpace.single j 1; D_j g(x) = Dg(x)(e_j) = fderiv ℝ g x e_j.
- (f ∗ g)(x) = ∫ f(t) g(x − t) dLⁿ(t) = convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) volume x.
- 1_B f = B.indicator f; “C^∞” = ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞).
- Integrals are Bochner integrals, equal to 0 for a non-integrable integrand.

Proof. Put B := B_ρ(x₀). Fix a C^∞ function a : ℝⁿ → ℝ with compact support and spt a ⊆ B, and fix j. Put v := e_j and d(x) := Da(x)(v) = D_j a(x).

1. (The function d.)
- a is C^∞, in particular C¹, so x ↦ Da(x) is continuous. Evaluation at the fixed vector v is continuous and linear, so d is continuous.
- Let x ∉ spt a. Then a vanishes on the open neighbourhood ℝⁿ ∖ spt a of x, so Da(x) = 0 and d(x) = 0. Hence {d ≠ 0} ⊆ spt a, and since spt a is closed, spt d ⊆ spt a ⊆ B.
- Consequently d has compact support (spt d is a closed subset of the compact set spt a), and d is integrable on ℝⁿ (continuous with compact support), in particular integrable on B.
- Also d(x) = 0 for every x ∉ B, and 1_B d = d.

2. (φ ∗ a is admissible for u.)
(a) φ is C^∞ with compact support and a is continuous, hence locally integrable. By differentiation under the integral sign, φ ∗ a is C^∞.
(b) φ and a both have compact support, so φ ∗ a has compact support.
(c) Suppose (φ ∗ a)(x) ≠ 0. Then the integrand t ↦ φ(t) a(x − t) is not identically 0, so x = s + t with φ(s) ≠ 0 and a(t) ≠ 0. That is, {φ ∗ a ≠ 0} ⊆ {φ ≠ 0} + {a ≠ 0}.
 For such s and t: s ∈ spt φ ⊆ B̄_ε(0), i.e. |s| ≤ ε; and t ∈ spt a ⊆ B, i.e. |t − x₀| < ρ. Hence |x − x₀| = |s + (t − x₀)| ≤ |s| + |t − x₀| ≤ ε + ρ.
 So {φ ∗ a ≠ 0} ⊆ B̄_{ρ+ε}(x₀). Since this ball is closed, spt(φ ∗ a) ⊆ B̄_{ρ+ε}(x₀) ⊆ U.
Thus φ ∗ a is C^∞, has compact support, and spt(φ ∗ a) ⊆ U.

3. (The derivative falls on a.) a is C¹ with compact support, and φ is locally integrable (it is continuous). So φ ∗ a is differentiable at every x, with D(φ ∗ a)(x) = ∫ φ(t) Da(x − t) dLⁿ(t), the convolution of φ with the continuous, compactly supported operator-valued function Da. Evaluation at the fixed vector v commutes with this integral, so D(φ ∗ a)(x)(v) = ∫ φ(t) Da(x − t)(v) dt = (φ ∗ d)(x). Hence, as functions, D_j(φ ∗ a) = φ ∗ d = φ ∗ (1_B d), the last equality because 1_B d = d (Step 1).

4. (Display (2).)
- Apply the hypothesis on u to the admissible function φ ∗ a of Step 2 and the index j: u(D_j(φ ∗ a)) = 0. By Step 3 this says u(φ ∗ (1_B d)) = 0.
- Hypothesis (1) with f := d (integrable on B by Step 1) gives ∫_B d θ dLⁿ = u(φ ∗ (1_B d)) = 0.
- The function x ↦ d(x) θ(x) vanishes for x ∉ B (Step 1), so its integral over B equals its integral over ℝⁿ. For the Bochner integral this needs no integrability: the integrand equals its restriction 1_B·(dθ), and B is measurable.
- Therefore ∫_{ℝⁿ} θ(x) D_j a(x) dLⁿ(x) = ∫_{ℝⁿ} d(x) θ(x) dLⁿ(x) = ∫_B d θ dLⁿ = 0.
Since a and j were arbitrary, the claim follows. ∎

Remark. The hypotheses 0 < ρ and 0 < ε, and any measurability or boundedness of θ, are not used and are not assumed.

Formalization notes (no new mathematics). Every name below is available under the frozen `import GMT.Ch06.Submission`. Do NOT add any import: the leaf gate rejects it. With L := ContinuousLinearMap.lsmul ℝ ℝ:
- Step 1: (ha1.continuous_fderiv one_ne_zero).clm_apply continuous_const, tsupport_fderiv_apply_subset ℝ v, hac.fderiv_apply ℝ v, Continuous.integrable_of_hasCompactSupport, image_eq_zero_of_notMem_tsupport, Set.indicator_eq_self.
- Step 2: hφc.contDiff_convolution_left L hφ ha.continuous.locallyIntegrable; hφc.convolution L hac; support_convolution_subset L with Set.mem_add, closure_minimal and isClosed_closedBall.
- Step 3: (hac.hasFDerivAt_convolution_right L hφli ha1 x).fderiv and convolution_precompR_apply L hφli (hac.fderiv ℝ) (ha1.continuous_fderiv one_ne_zero) x v.
- Step 4: setIntegral_eq_integral_of_forall_compl_eq_zero.
The following complete single-theorem proof of exactly this frozen type was compiled against the frozen Submission. It needs no new import, produces no warning, and #print axioms gives propext, Classical.choice, Quot.sound. It also passes a simulation of the leaf Git gate. It is a reference implementation; the prose proof above governs.

theorem constancy_mdc_weak_partials_vanish : <frozen type> := by
  intro n U u hu x₀ ρ ε hU φ hφ hφc hφs θ h1 a ha hac has j
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by exact_mod_cast le_top)
  set v : Eucl n := EuclideanSpace.single j (1 : ℝ) with hv
  set d : Eucl n → ℝ := fun x => fderiv ℝ a x v with hd
  have hdcont : Continuous d := (ha1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdsupp : tsupport d ⊆ tsupport a := tsupport_fderiv_apply_subset ℝ v
  have hdc : HasCompactSupport d := hac.fderiv_apply ℝ v
  have hdint : Integrable d volume := hdcont.integrable_of_hasCompactSupport hdc
  have hdzero : ∀ x, x ∉ ball x₀ ρ → d x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (has (hdsupp h)))
  have hind : (ball x₀ ρ).indicator d = d :=
    Set.indicator_eq_self.2 ((subset_tsupport d).trans (hdsupp.trans has))
  have hφli : LocallyIntegrable φ volume := hφ.continuous.locallyIntegrable
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convolution φ a (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hφc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hφ ha.continuous.locallyIntegrable
  have hcs : HasCompactSupport (convolution φ a (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hφc.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hac
  have hts : tsupport (convolution φ a (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆ U := by
    refine (closure_minimal ?_ isClosed_closedBall).trans hU
    intro x hx
    obtain ⟨s, hs, t, ht, rfl⟩ := Set.mem_add.1 (support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) hx)
    have hs' := hφs (subset_tsupport _ hs)
    have ht' := has (subset_tsupport _ ht)
    rw [mem_closedBall, dist_zero_right] at hs'
    rw [mem_ball, dist_eq_norm] at ht'
    rw [mem_closedBall, dist_eq_norm]
    calc ‖s + t - x₀‖ = ‖s + (t - x₀)‖ := by rw [add_sub_assoc]
      _ ≤ ‖s‖ + ‖t - x₀‖ := norm_add_le _ _
      _ ≤ ρ + ε := by linarith
  have hderiv : (fun x => fderiv ℝ (convolution φ a (ContinuousLinearMap.lsmul ℝ ℝ) volume) x v) =
      convolution φ ((ball x₀ ρ).indicator d) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    rw [hind]
    funext x
    rw [(hac.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hφli ha1 x).fderiv]
    exact convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hφli (hac.fderiv ℝ)
      (ha1.continuous_fderiv one_ne_zero) x v
  have hu0 := hu _ hsm hcs hts j
  rw [← hv, hderiv, h1 d hdint.integrableOn] at hu0
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball x₀ ρ)
    (fun x hx => by simp only [hd] at hdzero ⊢; rw [hdzero x hx, mul_zero])]
  simpa only [mul_comm] using hu0

## Key steps

1. d = D_j a is continuous, spt d ⊆ spt a ⊆ B, so d has compact support, is integrable, vanishes off B, and 1_B d = d.
2. φ ∗ a is C^∞ with compact support and spt(φ ∗ a) ⊆ B̄_{ρ+ε}(x₀) ⊆ U, since {φ ∗ a ≠ 0} ⊆ {φ ≠ 0} + {a ≠ 0} ⊆ B̄_ε(0) + B_ρ(x₀).
3. D_j(φ ∗ a) = φ ∗ d = φ ∗ (1_B d), using HasCompactSupport.hasFDerivAt_convolution_right and convolution_precompR_apply.
4. u(D_j(φ ∗ a)) = 0 together with (1) for f = d gives ∫_B d θ = 0; since dθ vanishes off B, ∫ θ D_j a = 0.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `diff GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean (identical); ls project/GMT/Ch06 in the snapshot`
- `rg -n 'theorem ae_tendsto_average_norm_sub|theorem exists_contDiff_tsupport_subset|theorem integral_comp_smul |theorem addHaar_closedBall |theorem _root_.HasCompactSupport.convolutionExists_right|theorem _root_.HasCompactSupport.hasFDerivAt_convolution_right|theorem convolution_precompR_apply|theorem integral_pos_iff_support_of_nonneg|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem exists_mem_of_measure_ne_zero_of_ae|theorem tsupport_fderiv_apply_subset|theorem support_convolution_subset' mathlib/Mathlib`
- `rg -n 'integral_div_left_eq_self|integral_sub_left_eq_self' mathlib/Mathlib/MeasureTheory/Group/Integral.lean; rg -n 'isUnifLocDoublingMeasure' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `rg -n 'contDiff_convolution_left|contDiff_convolution_right|ae_convolution_tendsto_right_of_locallyIntegrable|theorem ae_eq_zero_of_integral_contDiff_smul_eq_zero|theorem _root_.IsOpen.is_const_of_fderiv_eq_zero' mathlib/Mathlib`
- `rg -n 'ae_eq_const_of_weak|DistributionalConstancy|constancy_mdc' project (no match)`
- `grep -n 'theorem ae_eq_const_of_weak_coordinate_derivatives_zero' -B5 -A30 simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean; sed -n 1,304p of that file (fderiv_convolution_eq_zero, constancyMollifier via ContDiffBump.normed, ae_constancyMollifier_convolution_tendsto, ae_eq_const_on_ball); grep abbrev Euclidean Chapter08/Varifold.lean`
- `lake env lean #check files after `import GMT.Ch06.Submission` (Check1–Check4.lean): unknown = Poincare.SimonGMT.Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero, ContDiffBump.normed, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable, ContDiffBump.convolution_tendsto_right, MeasureTheory.ae_eq_zero_of_integral_contDiff_smul_eq_zero, Integrable.exists_hasCompactSupport_integral_sub_le; available = IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (instance for volume on Eucl n infers), VitaliFamily.ae_tendsto_average, exists_contDiff_tsupport_subset, Measure.integral_comp_smul, Measure.addHaar_closedBall, integral_sub_left_eq_self, Integrable.comp_sub_left, HasCompactSupport.convolutionExists_right/contDiff_convolution_left/right/hasFDerivAt_convolution_right, convolution_precompR_apply, IsOpen.is_const_of_fderiv_eq_zero, finrank_euclideanSpace_fin`
- `sed of /runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/leaf_verification.py (check_source_delta), prompts.py (RLCR_LEAN_TASK: preserve imports), runtime.py (_existing_lean_name_problem, reuse); git show cdfc95d (leaf candidate rejected for adding an import)`
- `python3 -I: lean_contract.validate_lean_statement on the 3 child types and the parent type; gmt-compare.contract_scope replay; lake env lean on generated challenge modules ChallengeA/B/C.lean`
- `lake env lean /tmp/dc-split-check/{Compose,ProveAC,ProveB,EndToEnd,EndToEnd2}.lean with #print axioms; python3 -I simulation of check_source_delta on each child insertion into the frozen Submission`
- `python3 -I scan of dag.json lean_name values (453 nodes) for the 3 proposed names (no match)`
- `book sources: chapter-06-source.txt lines 569–600 (2.34 printed proof), chapter-02-source.txt lines 530–545 (mollifier ϕ_σ), chapter-01-source.txt lines 927–935 (Corollary 3.17)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1-density-constancy-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1-density-constancy-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/prompts.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-06-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-01-source.txt`
- `/tmp/dc-split-check/ProveAC.lean`
- `/tmp/dc-split-check/ProveB.lean`
- `/tmp/dc-split-check/EndToEnd2.lean`

Snapshot pins project d8d46c95 and Mathlib 25730c7c. The frozen Submission.lean is byte-identical to Contract.lean.

Not available under the frozen `import GMT.Ch06.Submission`:
- the SimonGMT weak-constancy lemma ae_eq_const_of_weak_coordinate_derivatives_zero (DistributionalConstancy.lean:294), which the supplied Step 5 cites;
- ContDiffBump.normed;
- ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (BumpFunction/Convolution.lean:103);
- ae_eq_zero_of_integral_contDiff_smul_eq_zero (AEEqOfIntegralContDiff.lean:186).
The leaf gate forbids adding the import: check_source_delta rejects import, set_option and extra declarations, and commit cdfc95d shows an import-adding leaf rejected.

Available, and enough for an in-closure proof:
- Lebesgue points: IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (DensityTheorem.lean:150), with instance isUnifLocDoublingMeasureOfIsAddHaarMeasure (EqHaar.lean:550);
- exists_contDiff_tsupport_subset (FiniteDimension.lean:45);
- Measure.integral_comp_smul (Haar/NormedSpace.lean:92) and Measure.addHaar_closedBall (EqHaar.lean:500);
- integral_sub_left_eq_self, the additive form of Group/Integral.lean:163;
- the convolution API: convolutionExists_right (Convolution.lean:316), support_convolution_subset (:670), convolution_precompR_apply (:970), hasFDerivAt_convolution_right (ContDiff/Convolution.lean:61), contDiff_convolution_right/left (:420, :427);
- IsOpen.is_const_of_fderiv_eq_zero (MeanValue.lean:617).
The SimonGMT proof (fderiv_convolution_eq_zero, ae_eq_const_on_ball) served as the model for weak_constancy_ball.

Results:
- The 3 child types validate and elaborate in the comparator scope.
- Each child has a complete single-theorem Lean proof that compiles warning-free with no new import and passes the leaf-gate simulation.
- An end-to-end file proves the parent's exact frozen type from the children, with axioms propext, Classical.choice, Quot.sound only.
- The proposed names collide with nothing in the DAG (453 nodes), the project snapshot or simongmt.
