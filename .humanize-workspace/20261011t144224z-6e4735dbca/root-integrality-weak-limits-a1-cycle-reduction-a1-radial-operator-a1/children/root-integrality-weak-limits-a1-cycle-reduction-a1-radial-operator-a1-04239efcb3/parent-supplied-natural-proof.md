# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1.parametric_integral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 3 of the parent proof ("differentiation under the integral sign"), generalized from [0,1] to an arbitrary oriented interval [a,b] and filled in. The parent's currying induction (3(b)-(c)) is organized here as one induction on j that ranges over all complete codomains simultaneously. A Lean rendering of exactly this argument was compiled against the pinned snapshot, and #print axioms reports only propext, Classical.choice and Quot.sound.

Conventions. E := Eucl P is finite-dimensional, so its closed balls are compact. For a complete real normed space W and H : ℝ × E → W put:
- h_H(x) := ∫_a^b H(t,x) dt, the oriented interval integral `∫ t in a..b, H (t, x)`;
- ∂^jH(t,x) := iteratedFDeriv ℝ j (fun z => H (t, z)) x;
- H'(p) := (fderiv ℝ H p).comp ι ∈ E →L[ℝ] W, where ι := ContinuousLinearMap.inr ℝ ℝ E, so ι(h) = (0,h).
Write [[a,b]] := uIcc a b and Ι a b := uIoc a b; then Ι a b ⊆ [[a,b]] (uIoc_subset_uIcc).

1. (The partial derivative is again a smooth integrand.) Let W be complete and let H : ℝ × E → W be C^∞.
 (a) H' is C^∞. Since ∞ + 1 ≤ ∞, ContDiff.fderiv_right shows that fderiv ℝ H : ℝ × E → (ℝ × E →L[ℝ] W) is C^∞. The map p ↦ (fderiv ℝ H p).comp ι composes it with a fixed continuous linear map, so it is C^∞ (ContDiff.clm_comp with contDiff_const). The codomain E →L[ℝ] W is again complete. In particular H and H' are continuous.
 (b) For all t ∈ ℝ and x ∈ E, HasFDerivAt (fun z => H (t, z)) (H'(t,x)) x. Indeed:
 - H is differentiable at (t,x), being C^∞ with ∞ ≠ 0;
 - z ↦ (t,z) has derivative ι at x (hasFDerivAt_prodMk_right);
 - the chain rule (HasFDerivAt.comp) gives the derivative (fderiv ℝ H (t,x)).comp ι = H'(t,x).
 Hence fderiv ℝ (fun z => H (t, z)) = fun z => H'(t,z) for every t (HasFDerivAt.fderiv and funext).

2. (One differentiation under the integral sign.) Let W and H be as in Step 1 and let x₀ ∈ E. Then HasFDerivAt h_H (∫_a^b H'(t,x₀) dt) x₀.
 Proof. The set C := [[a,b]] ×ˢ closedBall x₀ 1 is compact (isCompact_uIcc.prod (isCompact_closedBall x₀ 1)) and H' is continuous. So there is K with ‖H'(p)‖ ≤ K for all p ∈ C (IsCompact.exists_bound_of_continuousOn). Apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le with μ = volume, F x t := H(t,x), F' x t := H'(t,x), s := ball x₀ 1 ∈ 𝓝 x₀, and bound ≡ K. Its hypotheses hold:
 (i) for every x, t ↦ H(t,x) is continuous, hence AEStronglyMeasurable for volume restricted to Ι a b;
 (ii) t ↦ H(t,x₀) is continuous, hence interval integrable on a..b;
 (iii) t ↦ H'(t,x₀) is continuous, hence AEStronglyMeasurable;
 (iv) for t ∈ Ι a b ⊆ [[a,b]] and x ∈ ball x₀ 1 ⊆ closedBall x₀ 1 we have (t,x) ∈ C, so ‖H'(t,x)‖ ≤ K;
 (v) the constant K is interval integrable;
 (vi) by Step 1(b), HasFDerivAt (fun x => H (t, x)) (H'(t,x)) x for every t and every x.
 The lemma gives the claim. Consequently h_H is differentiable on E and fderiv ℝ h_H = h_{H'}, that is, fderiv ℝ h_H x = ∫_a^b H'(t,x) dt for every x.

3. (Induction.) For j ∈ ℕ let Claim(j) be the statement: for every complete W and every C^∞ map H : ℝ × E → W,
 (i) h_H is C^j;
 (ii) (t,x) ↦ ∂^jH(t,x) is continuous on ℝ × E;
 (iii) iteratedFDeriv ℝ j h_H x = ∫_a^b ∂^jH(t,x) dt for every x.
 We prove Claim(j) for all j by induction on j. Because Claim(j) quantifies over all W and H, the induction hypothesis may be applied to a different codomain.
 (a) Case j = 0. Let Φ := (continuousMultilinearCurryFin0 ℝ E W).symm, a linear isometry equivalence W ≃ E[×0]→L[ℝ] W. For every f : E → W, iteratedFDeriv ℝ 0 f = Φ ∘ f (iteratedFDeriv_zero_eq_comp).
 - (i) C^0 means continuous (contDiff_zero). h_H is continuous by intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' applied to f x t := H(t,x), whose uncurried map (x,t) ↦ H(t,x), i.e. H ∘ swap, is continuous.
 - (ii) ∂^0H(t,x) = Φ(H(t,x)) is a composition of continuous maps.
 - (iii) iteratedFDeriv ℝ 0 h_H x = Φ(∫_a^b H(t,x) dt) = ∫_a^b Φ(H(t,x)) dt = ∫_a^b ∂^0H(t,x) dt. The middle step holds because a linear isometry commutes with the interval integral (LinearIsometry.intervalIntegral_comp_comm applied to Φ.toLinearIsometry).
 (b) Step j → j+1. Assume Claim(j) and let W and H be given. By Step 1(a), H' : ℝ × E → W' := E →L[ℝ] W is C^∞ and W' is complete. Claim(j) for (W', H') gives:
 - (i') h_{H'} is C^j;
 - (ii') (t,x) ↦ ∂^jH'(t,x) is continuous;
 - (iii') iteratedFDeriv ℝ j h_{H'} x = ∫_a^b ∂^jH'(t,x) dt.
 Let Ψ := (continuousMultilinearCurryRightEquiv' ℝ j E W).symm, a linear isometry equivalence E[×j]→L[ℝ](E →L[ℝ] W) ≃ E[×(j+1)]→L[ℝ] W. For every f : E → W and every x, iteratedFDeriv_succ_eq_comp_right gives iteratedFDeriv ℝ (j+1) f x = Ψ(iteratedFDeriv ℝ j (fun y => fderiv ℝ f y) x).
 - (i) By Step 2, h_H is differentiable and fderiv ℝ h_H = h_{H'}, which is C^j by (i'). So h_H is C^{j+1} by contDiff_succ_iff_fderiv. Here ((j+1 : ℕ) : WithTop ℕ∞) = j + 1 by Nat.cast_succ, and the clause "j = ω → analytic" is vacuous because j is finite.
 - (ii) By Step 1(b), fun y => fderiv ℝ (fun z => H (t, z)) y equals fun y => H'(t,y). Hence ∂^{j+1}H(t,x) = Ψ(∂^jH'(t,x)) for all (t,x), which is continuous by (ii') and the continuity of Ψ.
 - (iii) For x ∈ E:
 iteratedFDeriv ℝ (j+1) h_H x
 = Ψ(iteratedFDeriv ℝ j (fderiv ℝ h_H) x)
 = Ψ(iteratedFDeriv ℝ j h_{H'} x)
 = Ψ(∫_a^b ∂^jH'(t,x) dt), by (iii')
 = ∫_a^b Ψ(∂^jH'(t,x)) dt
 = ∫_a^b ∂^{j+1}H(t,x) dt, by the identity in (ii).
 The fourth equality holds because Ψ is a continuous linear map and t ↦ ∂^jH'(t,x) is continuous by (ii'), hence interval integrable (ContinuousLinearMap.intervalIntegral_comp_comm).
 This proves Claim(j+1).

4. (Conclusion.) Apply Claim(j) with W := V and H := G, for every j.
 - The second and third conjuncts of the statement are Claim(j)(ii) and Claim(j)(iii).
 - For the first conjunct, g = h_G is C^j for every j ∈ ℕ by Claim(j)(i), hence C^∞ (contDiff_infty, where ∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)). ∎

Implementation notes (all checked in a scratch build against the snapshot):
- Add `import Mathlib.Analysis.Calculus.ParametricIntervalIntegral` to Submission.lean.
- Prove Step 2 and Step 1(b) as auxiliary theorems `Submission.iwl_cr_ro_pi_step` and `Submission.iwl_cr_ro_pi_partial_fderiv`.
- Prove Claim(j) as the auxiliary theorem `Submission.iwl_cr_ro_pi_claim`, stated as `∀ j : ℕ, ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] (H : ℝ × Eucl P → W), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H → …` and proved by `intro j; induction j`.
- The C^∞ property of H' is `(hH.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_comp contDiff_const`.
- In 3(b)(iii), `LinearIsometry.intervalIntegral_comp_comm` on Ψ.toLinearIsometry fails with an instance-path mismatch (ContinuousMultilinearMap.seminormedAddCommGroup'). Use `((Ψ : _ →L[ℝ] _)).intervalIntegral_comp_comm hint` instead, then normalize the coercions with `simp only [ContinuousLinearMap.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe] at e`.
- In the base case, `LinearIsometry.intervalIntegral_comp_comm` with Φ.toLinearIsometry works.

Appendix — verified Lean rendering of the proof above. It was compiled against the pinned snapshot in the Submission.lean layout, i.e. inside `namespace GMT.Ch06` after the contract's section, with the contract's `open`s. A comparator-style check `theorem … : (frozen type) := by exact Submission.<name>`, run in the replayed contract scope, also passes. `#print axioms` reports only propext, Classical.choice and Quot.sound. Required import: `import Mathlib.Analysis.Calculus.ParametricIntervalIntegral`.

```lean
theorem Submission.iwl_cr_ro_pi_step (P : ℕ) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] (H : ℝ × Eucl P → W) (a b : ℝ) (hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H)
    (x₀ : Eucl P) :
    HasFDerivAt (fun x : Eucl P => ∫ t in a..b, H (t, x))
      (∫ t in a..b, (fderiv ℝ H (t, x₀)).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P))) x₀ := by
  set H' : ℝ × Eucl P → (Eucl P →L[ℝ] W) :=
    fun p => (fderiv ℝ H p).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P)) with hH'
  have hH'c : Continuous H' :=
    ((hH.continuous_fderiv (by simp)).clm_comp continuous_const)
  obtain ⟨K, hK⟩ : ∃ K, ∀ p ∈ uIcc a b ×ˢ closedBall x₀ 1, ‖H' p‖ ≤ K :=
    (isCompact_uIcc.prod (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn
      hH'c.continuousOn
  have hHc : Continuous H := hH.continuous
  have hdiff : ∀ t : ℝ, ∀ x : Eucl P, HasFDerivAt (fun z : Eucl P => H (t, z)) (H' (t, x)) x := by
    intro t x
    have h1 : HasFDerivAt H (fderiv ℝ H (t, x)) (t, x) :=
      (hH.differentiable (by simp) (t, x)).hasFDerivAt
    exact h1.comp x (hasFDerivAt_prodMk_right t x)
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun x t => H (t, x)) (F' := fun x t => H' (t, x)) (x₀ := x₀) (bound := fun _ => K)
    (s := ball x₀ 1) (ball_mem_nhds x₀ one_pos)
    (Eventually.of_forall fun x =>
      (hHc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    ((hHc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
    ((hH'c.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    (Eventually.of_forall fun t ht x hx =>
      hK (t, x) ⟨uIoc_subset_uIcc ht, ball_subset_closedBall hx⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun t _ x _ => hdiff t x)

theorem Submission.iwl_cr_ro_pi_partial_fderiv (P : ℕ) (W : Type) [NormedAddCommGroup W]
    [NormedSpace ℝ W] (H : ℝ × Eucl P → W) (hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H) (t : ℝ) :
    fderiv ℝ (fun z : Eucl P => H (t, z)) =
      fun z => (fderiv ℝ H (t, z)).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P)) := by
  funext x
  have h1 : HasFDerivAt H (fderiv ℝ H (t, x)) (t, x) :=
    (hH.differentiable (by simp) (t, x)).hasFDerivAt
  exact (h1.comp x (hasFDerivAt_prodMk_right t x)).fderiv

theorem Submission.iwl_cr_ro_pi_claim (P : ℕ) (a b : ℝ) : ∀ j : ℕ, ∀ (W : Type)
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] (H : ℝ × Eucl P → W),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H →
    ContDiff ℝ j (fun x : Eucl P => ∫ t in a..b, H (t, x)) ∧
    Continuous (fun p : ℝ × Eucl P => iteratedFDeriv ℝ j (fun z : Eucl P => H (p.1, z)) p.2) ∧
    ∀ x : Eucl P, iteratedFDeriv ℝ j (fun y : Eucl P => ∫ t in a..b, H (t, y)) x =
      ∫ t in a..b, iteratedFDeriv ℝ j (fun z : Eucl P => H (t, z)) x := by
  intro j
  induction j with
  | zero =>
    intro W _ _ _ H hH
    have hHc : Continuous H := hH.continuous
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.cast_zero, contDiff_zero]
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun x t => H (t, x)) (hHc.comp continuous_swap) a b
    · simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def]
      exact (continuousMultilinearCurryFin0 ℝ (Eucl P) W).symm.continuous.comp hHc
    · intro x
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact ((continuousMultilinearCurryFin0 ℝ (Eucl P) W).symm.toLinearIsometry.intervalIntegral_comp_comm
        (fun t => H (t, x))).symm
  | succ j ih =>
    intro W _ _ _ H hH
    set H' : ℝ × Eucl P → (Eucl P →L[ℝ] W) :=
      fun p => (fderiv ℝ H p).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P)) with hH'
    have hH'smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H' :=
      (hH.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_comp contDiff_const
    obtain ⟨ih1, ih2, ih3⟩ := ih (Eucl P →L[ℝ] W) H' hH'smooth
    have hg : fderiv ℝ (fun x : Eucl P => ∫ t in a..b, H (t, x)) =
        fun x => ∫ t in a..b, H' (t, x) := by
      funext x
      exact (Submission.iwl_cr_ro_pi_step P W H a b hH x).fderiv
    have hgd : Differentiable ℝ (fun x : Eucl P => ∫ t in a..b, H (t, x)) :=
      fun x => (Submission.iwl_cr_ro_pi_step P W H a b hH x).differentiableAt
    have hpart : ∀ t : ℝ, fderiv ℝ (fun z : Eucl P => H (t, z)) = fun z => H' (t, z) :=
      fun t => Submission.iwl_cr_ro_pi_partial_fderiv P W H hH t
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
      refine ⟨hgd, fun h => absurd h (by simp), ?_⟩
      rw [hg]
      exact ih1
    · have : (fun p : ℝ × Eucl P => iteratedFDeriv ℝ (j + 1) (fun z : Eucl P => H (p.1, z)) p.2) =
          fun p => (continuousMultilinearCurryRightEquiv' ℝ j (Eucl P) W).symm
            (iteratedFDeriv ℝ j (fun z : Eucl P => H' (p.1, z)) p.2) := by
        funext p
        rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
        congr 2
        exact hpart p.1
      rw [this]
      exact (continuousMultilinearCurryRightEquiv' ℝ j (Eucl P) W).symm.continuous.comp ih2
    · intro x
      rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
      have : (fun y => fderiv ℝ (fun x : Eucl P => ∫ t in a..b, H (t, x)) y) =
          fun x => ∫ t in a..b, H' (t, x) := hg
      rw [this, ih3 x]
      have hint : IntervalIntegrable
          (fun t : ℝ => iteratedFDeriv ℝ j (fun z : Eucl P => H' (t, z)) x) volume a b :=
        (ih2.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
      have e := ((continuousMultilinearCurryRightEquiv' ℝ j (Eucl P) W).symm :
          (Eucl P [×j]→L[ℝ] (Eucl P →L[ℝ] W)) →L[ℝ] (Eucl P [×(j + 1)]→L[ℝ] W)).intervalIntegral_comp_comm hint
      simp only [ContinuousLinearMap.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        ContinuousLinearEquiv.coe_coe] at e
      rw [← e]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
      congr 2
      exact (hpart t).symm

theorem Submission.iwl_cr_ro_intervalIntegral_contDiff :
    (∀ (P : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (G : ℝ × Eucl P → V) (a b : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Eucl P => ∫ t in a..b, G (t, x)) ∧ (∀ j : ℕ, Continuous (fun p : ℝ × Eucl P => iteratedFDeriv ℝ j (fun z : Eucl P => G (p.1, z)) p.2)) ∧ ∀ (j : ℕ) (x : Eucl P), iteratedFDeriv ℝ j (fun y : Eucl P => ∫ t in a..b, G (t, y)) x = ∫ t in a..b, iteratedFDeriv ℝ j (fun z : Eucl P => G (t, z)) x) := by
  intro P V _ _ _ G a b hG
  exact ⟨contDiff_infty.2 fun n => (Submission.iwl_cr_ro_pi_claim P a b n V G hG).1,
    fun j => (Submission.iwl_cr_ro_pi_claim P a b j V G hG).2.1,
    fun j x => (Submission.iwl_cr_ro_pi_claim P a b j V G hG).2.2 x⟩
```

## Key steps

1. For a C^∞ H : ℝ × E → W, the x-partial derivative H'(t,x) = DH(t,x) ∘ inr is again a C^∞ integrand with values in the complete space E →L W, and HasFDerivAt (H(t,·)) (H'(t,x)) x by the chain rule.
2. One differentiation under the integral sign: bound ‖H'‖ ≤ K on the compact set uIcc a b × closedBall x₀ 1, then apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le. This gives fderiv h_H = h_{H'}.
3. Induction on j over all complete codomains: h_H is C^j, (t,x) ↦ ∂^jH(t,x) is continuous, and D^j h_H = ∫ ∂^jH. Base case via continuousMultilinearCurryFin0; step via iteratedFDeriv_succ_eq_comp_right and commuting the currying isometry with the integral.
4. C^j for every j gives C^∞ (contDiff_infty); continuity and the derivative formula are the inductive invariants.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (project_commit d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; sha256sum GMT/Ch06/Contract.lean`
- `rg -n "(theorem|lemma|def|abbrev) [A-Za-z_.']*<name>\b" mathlib/Mathlib for <name> in hasFDerivAt_integral_of_dominated_of_fderiv_le, norm_iteratedFDeriv_le_of_bilinear, curryLeftLI, norm_curryLeft, curryLeft_apply_apply, iteratedFDeriv_comp_right, continuous_iteratedFDeriv, iteratedFDeriv_succ_eq_comp_left, continuous_parametric_intervalIntegral_of_continuous, contDiff_of_differentiable_iteratedFDeriv, intervalIntegral_comp_comm, norm_compContinuousLinearMap_le, norm_integral_le_of_norm_le_const, contDiff_parametric_integral_of_contDiff, contDiff_parametric_primitive_of_contDiff`
- `rg -n 'contDiff_parametric|ContDiff.*intervalIntegral|contDiff_integral|iteratedFDeriv_integral|integral_iteratedFDeriv|contDiffOn_parametric|fderiv_integral|hasFDerivAt_integral\b' mathlib/Mathlib`
- `rg -n 'parametric_primitive|parametric_integral|ParametricIntegral' mathlib/Mathlib`
- `rg -n 'norm_iteratedFDeriv_le_of_bilinear_of_le_one|norm_iteratedFDeriv_clm_apply|iteratedFDeriv_const_smul_apply|iteratedFDeriv_const_of_ne|theorem fderiv_id|prod_le_one₀|iteratedFDeriv_succ_eq_comp_right|contDiff_succ_iff_fderiv|contDiff_infty|iteratedFDeriv_one_apply|norm_iteratedFDeriv_one|intervalIntegral_comp_comm' mathlib/Mathlib`
- `rg -n 'def apply' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Topology.lean`
- `rg -n 'iteratedFDeriv_fixedSupportParameterSlice|intervalIntegral|∫ t in' simongmt/Poincare/SimonGMT; grep -n 'abbrev|^def' simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `python3: dag.json node metadata and lean_name scan (iwl_cr_*, radial, lean_statements containing ∫ together with fderiv/iteratedFDeriv/ContDiff); grep -rl iwl_cr_ro_ over dag.json, nodes/ and GMT/; git grep -l iwl_cr_ro_ over all 619 ref tips`
- `git show 2f3657605e574458d48b2cd837f262ae2f392816:GMT/Ch06/Submission.lean (imports and Submission.X declaration layout of an accepted candidate)`
- `python3 -I /tmp/ro_split/scripts/gen.py (verifier gmt-compare.py child_modules + lean_contract.validate_lean_statement); lake env lean /tmp/ro_split/gen/*__NodeChallenge.lean`
- `lake env lean /tmp/ro_split/scratch/{Assembly,Full,InstCheck,ImportCheck}.lean and /tmp/ro_split/snip/Snip{A,B1,B2}.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/ParametricCurrentContinuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ro_split/scripts/gen.py`
- `/tmp/ro_split/scratch/Assembly.lean`
- `/tmp/ro_split/scratch/Full.lean`
- `/tmp/ro_split/scratch/InstCheck.lean`
- `/tmp/ro_split/scratch/ImportCheck.lean`
- `/tmp/ro_split/snip/SnipA.lean`
- `/tmp/ro_split/snip/SnipB1.lean`
- `/tmp/ro_split/snip/SnipB2.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. Its Ch06 Contract.lean is byte-identical to the workspace Contract.lean (sha256 ea3ee0dd…).

Missing obligation. The snapshot Mathlib has only first-order differentiation under an interval integral (`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`, Analysis/Calculus/ParametricIntervalIntegral.lean:55) and continuity of parametric integrals (`continuous_parametric_intervalIntegral_of_continuous'`, DominatedConvergence.lean:619). There is no lemma for C^∞ smoothness of x ↦ ∫ G(t,x) dt or for iterated derivatives under the integral: the searches for contDiff_parametric*, ContDiff.*intervalIntegral and iteratedFDeriv_integral found nothing. So the all-order statement is a genuinely missing, reusable obligation, which becomes child parametric_integral.

Available Mathlib tools:
- Leibniz bounds `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear(_of_le_one)` (ContDiff/Bounds.lean:202/226);
- curryLeft, curryLeftLI, norm_curryLeft and curryLeft_apply_apply (Normed/Module/Alternating/Curry.lean);
- `ContinuousLinearMap.iteratedFDeriv_comp_right` (ContDiff/Basic.lean:461);
- `iteratedFDeriv_succ_eq_comp_right` and `iteratedFDeriv_one_apply` (FTaylorSeries.lean);
- `contDiff_succ_iff_fderiv` and `contDiff_infty` (ContDiff/Defs.lean);
- `ContinuousAlternatingMap.apply` and `ContinuousMultilinearMap.apply` (Topology/Algebra/Module/{Alternating,Multilinear}/Topology.lean).

Imports. ParametricIntervalIntegral and ContDiff.Bounds are not imported by GMT.Ch06.Submission (an #check reports unknown constants), so children 1 and 3 add those imports. The accepted candidate at commit 2f36576 also adds imports to Submission.lean and declares `theorem Submission.X` inside namespace GMT.Ch06.

SimonGMT. Covector and DifferentialForm are abbrevs (Chapter06/Forms.lean:31/37). `iteratedFDeriv_fixedSupportParameterSlice` (Chapter06/ParametricCurrentContinuity.lean:76) uses the same partial-derivative-by-inclusion pattern, but SimonGMT has no smoothness result for parametric integrals.

DAG and names. No DAG node supplies a parametric-integral smoothness lemma or the radial integrand facts. The names iwl_cr_ro_* and the helper prefixes iwl_cr_ro_pi_ / iwl_cr_ro_ib_ occur nowhere in dag.json, nodes/, GMT/ or any of the 619 git ref tips.

Lean checks:
- The three frozen child types, generated through the verifier's own child_modules / validate_lean_statement path, elaborate in the replayed contract scope.
- Assembly.lean proves the parent's exact frozen type from the three children, which are sorried there.
- Full.lean and Snip{A,B1,B2}.lean prove all three children and the parent; #print axioms gives [propext, Classical.choice, Quot.sound], and the comparator-style `exact Submission.<name>` targets pass.
- An independent reviewer agent re-ran these builds and accepted the split.

Public citations for the standard mathematics: differentiation under the integral sign (Dieudonné, Foundations of Modern Analysis, §8.11) and the radial homotopy operator of the Poincaré lemma (Spivak, Calculus on Manifolds, Thm 4-11).
