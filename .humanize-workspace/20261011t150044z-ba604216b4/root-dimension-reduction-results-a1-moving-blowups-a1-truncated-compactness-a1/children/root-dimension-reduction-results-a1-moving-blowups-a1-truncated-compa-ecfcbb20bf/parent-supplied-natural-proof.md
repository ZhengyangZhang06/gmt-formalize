# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.truncated_compactness-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.truncated_compactness-a1.truncation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 3 (Simon Ch. 6, 2.9 and 3.2: the restriction T⌞B of T = τ(M, θ, ξ) to a ball is τ(M ∩ B, θ, ξ), chapter-06.txt lines 284–288 and 755–767; the bound on its boundary is the slice estimate 4.6–4.10, lines 1335–1376, which the parent supplies through hypotheses (ii)–(iii)).
Siblings: im_calculus (IMC), part (b); imrep_restriction (RS), part (c); eval_mass_bound (E1).
Notation: n := m + 1; Hⁿ := μHE[n]; M := R.carrier, θ := R.mult, ξ := R.orient, μ := R.measure; B_r := ball(0, r); ⟨α, ξ(x)⟩ := ξ(x)(α); |α| := covectorEuclideanNorm α; 𝒟^k(V) := TestFormOn V k (a form α belongs to 𝒟^k(V) iff it is smooth, compactly supported and tsupport α ⊆ V).

0. Preliminary facts.
 (F1) closedBall(0, ρ) ⊆ B_s ⊆ U since ρ < s; so B_ρ ⊆ U, and closedBall(0, ρ) is a compact subset of U.
 (F2) |tα| = |t|·|α| for t ∈ ℝ and every covector α: (tα)(e_I) = t·α(e_I), so Σ_I [I strictly increasing](tα)(e_I)² = t²·Σ_I [I strictly increasing]α(e_I)², and √(t²X) = |t|√X for X ≥ 0.
 (F3) If x ∉ tsupport α then α(x) = 0 (image_eq_zero_of_notMem_tsupport), hence ⟨α(x), ξ(x)⟩ = 0 by linearity of ξ(x).

1. (Restriction in U.) Apply (IMC)(b) to R and the Borel set E := B_ρ (U is open): there is an IMRep R₁ in U with carrier M ∩ B_ρ, multiplicity θ and orientation ξ (the current it represents is not needed). By (RS)(c) applied to R, E = B_ρ and R′ := R₁: R₁.measure = μ⌞B_ρ, and R₁.action(α) = ∫_{B_ρ} ⟨α, ξ⟩ dμ for every n-form α (no regularity required).

2. (The same data as a representation in ℝ^P.) Let R₂ be the IMRep in ℝ^P with carrier M ∩ B_ρ, multiplicity θ and orientation ξ. Its fields measurableSet_carrier, rectifiable, measurable_mult, mult_pos, aestronglyMeasurable_orient and orients only involve carrier, multiplicity, orientation and Hⁿ, so they are those of R₁; carrier ⊆ ℝ^P is trivial. Local integrability: for every compact K, (M ∩ B_ρ) ∩ K ⊆ M ∩ closedBall(0, ρ), so ∫_{(M∩B_ρ)∩K} θ dHⁿ ≤ ∫_{M∩closedBall(0,ρ)} θ dHⁿ < ∞, by monotonicity of the lower integral in the domain (lintegral_mono_set) and R.locallyIntegrable_mult for the compact set closedBall(0, ρ) ⊆ U (F1).

3. (The current Ŝ.) Apply (IMC)(b) to R₂ (domain ℝ^P, open) and E := ℝ^P: there are Ŝ ∈ 𝒟_n(ℝ^P) and an IMRep R′ in ℝ^P representing Ŝ, with carrier (M ∩ B_ρ) ∩ ℝ^P = M ∩ B_ρ, multiplicity θ and orientation ξ. IMRep.measure and IMRep.action depend only on carrier, multiplicity and orientation, so R′.measure = R₁.measure = μ⌞B_ρ (the second claim), and for every ω ∈ 𝒟ⁿ(ℝ^P):
 Ŝ(ω) = R′.action(ω) = R₁.action(ω) = ∫_{B_ρ} ⟨ω, ξ⟩ dμ.   (∗)

4. (Agreement.) Let ω ∈ 𝒟ⁿ(ℝ^P) with tsupport ω ⊆ B_ρ. Then ω is smooth with compact support and tsupport ω ⊆ U (F1), so ω ∈ 𝒟ⁿ(U) and currentEval(S, ω) = S(ω) (definition of currentEval, positive branch). As R represents S, S(ω) = R.action(ω); by (RS)(c) applied to R, E = ℝ^P and R′ := R (R.carrier = R.carrier ∩ ℝ^P), R.action(ω) = ∫_{ℝ^P} ⟨ω, ξ⟩ dμ. For x ∉ B_ρ we have x ∉ tsupport ω, so the integrand vanishes (F3), and ∫_{ℝ^P} ⟨ω, ξ⟩ dμ = ∫_{B_ρ} ⟨ω, ξ⟩ dμ (setIntegral_eq_integral_of_forall_compl_eq_zero). By (∗) this is Ŝ(ω).

5. (No boundary inside B_ρ.) Let β ∈ 𝒟^m(ℝ^P) with tsupport β ⊆ B_ρ. Then ∂Ŝ(β) = Ŝ(dβ) (GeometricCurrentOn.boundary_apply; dβ = exteriorDerivative β is a test form, exteriorDerivative_isTestForm), and tsupport dβ ⊆ tsupport β ⊆ B_ρ (tsupport_exteriorDerivative_subset). By step 4, Ŝ(dβ) = currentEval(S, dβ) = S(dβ), with dβ ∈ 𝒟ⁿ(U). Also β ∈ 𝒟^m(U) (tsupport β ⊆ B_ρ ⊆ U), and S(dβ) = ∂S(β) because the exterior derivative of β ∈ 𝒟^m(U) is the same form dβ (boundary_apply). Since tsupport β ⊆ B_ρ ⊆ B_s, hypothesis (i) gives ∂S(β) = 0. Hence ∂Ŝ(β) = 0.

6. (Cut-off.) Put s′ := (ρ + s)/2, so ρ < s′ < s, and let χ : ℝ^P → ℝ be the smooth bump function centred at 0 with inner radius ρ and outer radius s′ (Mathlib ContDiffBump): χ is C^∞, 0 ≤ χ ≤ 1, χ = 1 on closedBall(0, ρ), tsupport χ = closedBall(0, s′) ⊆ B_s, χ has compact support, and for every x ∈ B_ρ, χ = 1 on a neighbourhood of x (ContDiffBump.eventuallyEq_one_of_mem_ball). Let β ∈ 𝒟^m(ℝ^P) with |β(x)| ≤ 1 for all x, and γ(x) := χ(x)·β(x).
 (a) γ is smooth (product of smooth maps) with compact support (HasCompactSupport.smul_right), and tsupport γ ⊆ tsupport χ ⊆ B_s ⊆ U (tsupport_smul_subset_left). Thus γ ∈ 𝒟^m(U) and tsupport γ ⊆ B_s.
 (b) |γ(x)| = χ(x)·|β(x)| ≤ 1 for every x, by (F2) and 0 ≤ χ ≤ 1.
 (c) For x ∈ B_ρ, γ = β on a neighbourhood of x, so dγ(x) = dβ(x): the exterior derivative at x depends only on the germ at x (Filter.EventuallyEq.extDeriv_eq).

7. (Boundary mass.) With β, γ as in step 6:
 ∂Ŝ(β) = Ŝ(dβ) = ∫_{B_ρ} ⟨dβ, ξ⟩ dμ   by (∗)
  = ∫_{B_ρ} ⟨dγ, ξ⟩ dμ   (the integrands agree on B_ρ by 6(c); setIntegral_congr_fun)
  = A(dγ)   (hypothesis (ii) for the test form dγ ∈ 𝒟ⁿ(U))
  = ∂A(γ)   (boundary_apply).
 By (E1) applied in U to the current ∂A ∈ 𝒟_m(U), the set W := B_s, the form γ and r := 1 — legitimate by (iii), 6(a) and 6(b) — |∂A(γ)| ≤ (M_{B_s}(∂A)).toReal. Hence ofReal(∂Ŝ(β)) ≤ ofReal((M_{B_s}(∂A)).toReal) = M_{B_s}(∂A), the last equality by (iii). The forms admissible for M_{ℝ^P}(∂Ŝ) are exactly such β (the support condition tsupport β ⊆ ℝ^P is vacuous), so taking the supremum (sSup_le) gives M_{ℝ^P}(∂Ŝ) ≤ M_{B_s}(∂A).

8. (Conclusion.) Ŝ and R′ satisfy all five claims: representation and weight (step 3), agreement (step 4), vanishing boundary inside B_ρ (step 5) and the boundary mass bound (step 7). ∎

Appendix (verified Lean realization of the numbered proof above; not part of the proof). Compiled in this decomposition session with Lean v4.35.0-rc3, Mathlib 25730c7c and SimonGMT 2b366308 after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the frozen contract's `open` commands (after its `noncomputable section ... end`). No extra import is needed. The sibling declarations are used through their accepted names `Submission.<lean_name>`; with them as hypotheses `#print axioms` reports only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.dimred_mbl_tc_truncate_at_good_radius : ∀ (P m : ℕ) (U : Set (Euclid P)) (S A : GeometricCurrentOn U (m + 1)) (R : IMRep U (m + 1)) (ρ s : ℝ), IsOpen U → R.Represents S → (∀ β : TestFormOn U m, tsupport (β : DifferentialForm (Euclid P) m) ⊆ ball 0 s → S.boundary β = 0) → 0 < ρ → ρ < s → ball (0 : Euclid P) s ⊆ U → (∀ ω : TestFormOn U (m + 1), A ω = ∫ x in ball (0 : Euclid P) ρ, R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂R.measure) → A.boundary.massOn (ball 0 s) ≠ ∞ → ∃ (Ŝ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R' : IMRep (univ : Set (Euclid P)) (m + 1)), R'.Represents Ŝ ∧ R'.measure = R.measure.restrict (ball 0 ρ) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ ball 0 ρ → Ŝ ω = currentEval S (ω : DifferentialForm (Euclid P) (m + 1))) ∧ (∀ β : TestFormOn (univ : Set (Euclid P)) m, tsupport (β : DifferentialForm (Euclid P) m) ⊆ ball 0 ρ → Ŝ.boundary β = 0) ∧ Ŝ.boundary.massOn univ ≤ A.boundary.massOn (ball 0 s) := by
  have hE1 := Submission.cmr_abs_apply_le_massOn
  have hIMC := Submission.cmc_imRep_locality_restrict_sub
  have hRS := Submission.lcmp_imRep_measure_restrict
  intro P m U S A R ρ s hU hSR hSb hρ hρs hsU hA hAfin
  have hcb : closedBall (0 : Euclid P) ρ ⊆ U := (closedBall_subset_ball hρs).trans hsU
  -- Step 1: restriction of R to ball 0 ρ, in U
  obtain ⟨-, R₁, -, hR₁c, hR₁m, hR₁o⟩ := hIMC.2.1 P (m + 1) U R (ball 0 ρ) hU measurableSet_ball
  -- Step 2: the same data as an IMRep in ℝ^P
  let R₂ : IMRep (univ : Set (Euclid P)) (m + 1) :=
    { carrier := R₁.carrier
      mult := R₁.mult
      orient := R₁.orient
      measurableSet_carrier := R₁.measurableSet_carrier
      carrier_subset := subset_univ _
      rectifiable := R₁.rectifiable
      measurable_mult := R₁.measurable_mult
      mult_pos := R₁.mult_pos
      locallyIntegrable_mult := fun K _ _ => by
        refine ne_top_of_le_ne_top
          (R.locallyIntegrable_mult _ (isCompact_closedBall 0 ρ) hcb) ?_
        rw [hR₁c, hR₁m]
        exact lintegral_mono_set (fun x hx => ⟨hx.1.1, ball_subset_closedBall hx.1.2⟩)
      aestronglyMeasurable_orient := R₁.aestronglyMeasurable_orient
      orients := R₁.orients }
  -- Step 3: the current represented in ℝ^P
  obtain ⟨Ŝ, R', hR'rep, hR'c, hR'm, hR'o⟩ :=
    hIMC.2.1 P (m + 1) univ R₂ univ isOpen_univ MeasurableSet.univ
  -- Step 4: weight and action
  obtain ⟨-, -, hrestr⟩ := hRS P (m + 1) U R
  obtain ⟨hmeas₁, hact₁⟩ := hrestr (ball 0 ρ) R₁ measurableSet_ball hR₁c hR₁m hR₁o
  have hR'meas : R'.measure = R.measure.restrict (ball 0 ρ) := by
    rw [← hmeas₁]
    unfold IMRep.measure
    rw [hR'c, hR'm, inter_univ]
  have hact : ∀ ω : DifferentialForm (Euclid P) (m + 1),
      R'.action ω = ∫ x in ball (0 : Euclid P) ρ, R.orient x (ω x) ∂R.measure := by
    intro ω
    rw [← hact₁ ω]
    unfold IMRep.action
    rw [hR'c, hR'm, hR'o, inter_univ]
  have hŜ : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1),
      Ŝ ω = ∫ x in ball (0 : Euclid P) ρ,
        R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂R.measure := fun ω => by
    rw [hR'rep ω, hact]
  -- Step 5: agreement
  have hagree : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1),
      tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ ball 0 ρ →
        Ŝ ω = currentEval S (ω : DifferentialForm (Euclid P) (m + 1)) := by
    intro ω hω
    have hωU : IsTestForm (ω : DifferentialForm (Euclid P) (m + 1)) ∧
        tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ U :=
      ⟨ω.property.1, hω.trans (ball_subset_closedBall.trans hcb)⟩
    rw [currentEval, dif_pos hωU, hSR, hŜ,
      (hrestr univ R MeasurableSet.univ (by simp) rfl rfl).2, Measure.restrict_univ]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
    show R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) = 0
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hω h)), map_zero]
  -- Step 6: vanishing boundary inside
  have hbdry : ∀ β : TestFormOn (univ : Set (Euclid P)) m,
      tsupport (β : DifferentialForm (Euclid P) m) ⊆ ball 0 ρ → Ŝ.boundary β = 0 := by
    intro β hβ
    have hdβ : tsupport (exteriorDerivative (β : DifferentialForm (Euclid P) m)) ⊆ ball 0 ρ :=
      (tsupport_exteriorDerivative_subset _).trans hβ
    have hβU : (β : DifferentialForm (Euclid P) m) ∈ TestFormOn U m :=
      ⟨β.property.1, hβ.trans (ball_subset_closedBall.trans hcb)⟩
    rw [GeometricCurrentOn.boundary_apply, hagree _ hdβ]
    have hdU : IsTestForm (exteriorDerivative (β : DifferentialForm (Euclid P) m)) ∧
        tsupport (exteriorDerivative (β : DifferentialForm (Euclid P) m)) ⊆ U :=
      ⟨exteriorDerivative_isTestForm β.property.1,
        hdβ.trans (ball_subset_closedBall.trans hcb)⟩
    have := hSb ⟨_, hβU⟩ (hβ.trans (ball_subset_ball hρs.le))
    rw [GeometricCurrentOn.boundary_apply] at this
    show currentEval S (exteriorDerivative (β : DifferentialForm (Euclid P) m)) = 0
    rw [currentEval, dif_pos hdU]
    exact this
  -- Step 7: cutoff
  have hmid : ρ < (ρ + s) / 2 := by linarith
  let χ : ContDiffBump (0 : Euclid P) := ⟨ρ, (ρ + s) / 2, hρ, hmid⟩
  have hχsupp : tsupport (χ : Euclid P → ℝ) ⊆ ball 0 s := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by show (ρ + s) / 2 < s; linarith)
  have hsmul : ∀ (c : ℝ) (α : Covector (Euclid P) m),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun I _ => ?_)
    split_ifs <;> simp [ContinuousAlternatingMap.smul_apply, mul_pow]
  -- Step 8: boundary mass
  have hmass : Ŝ.boundary.massOn univ ≤ A.boundary.massOn (ball 0 s) := by
    unfold GeometricCurrentOn.massOn
    apply sSup_le
    rintro _ ⟨β, hβ, rfl⟩
    show ENNReal.ofReal (Ŝ.boundary β) ≤ _
    set b : DifferentialForm (Euclid P) m := (β : DifferentialForm (Euclid P) m) with hb
    let γ : DifferentialForm (Euclid P) m := fun x => (χ x) • b x
    have hγtest : IsTestForm γ := by
      refine ⟨?_, ?_⟩
      · exact (χ.contDiff).smul β.property.1.1
      · exact χ.hasCompactSupport.smul_right
    have hγsupp : tsupport γ ⊆ ball 0 s :=
      (tsupport_smul_subset_left (fun x => χ x) b).trans hχsupp
    have hγU : γ ∈ TestFormOn U m := ⟨hγtest, hγsupp.trans hsU⟩
    have hγnorm : ∀ x, covectorEuclideanNorm (γ x) ≤ 1 := by
      intro x
      show covectorEuclideanNorm (χ x • b x) ≤ 1
      rw [hsmul, abs_of_nonneg (χ.nonneg)]
      calc χ x * covectorEuclideanNorm (b x) ≤ 1 * 1 :=
            mul_le_mul χ.le_one (hβ.2 x) (covectorEuclideanNorm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have hloc : ∀ x ∈ ball (0 : Euclid P) ρ, exteriorDerivative b x = exteriorDerivative γ x := by
      intro x hx
      have h1 : (χ : Euclid P → ℝ) =ᶠ[𝓝 x] 1 := χ.eventuallyEq_one_of_mem_ball hx
      have h2 : b =ᶠ[𝓝 x] γ := by
        filter_upwards [h1] with y hy
        show b y = χ y • b y
        rw [hy]; simp
      exact h2.extDeriv_eq
    have hkey : Ŝ.boundary β = A.boundary ⟨γ, hγU⟩ := by
      rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply, hŜ, hA]
      refine setIntegral_congr_fun measurableSet_ball (fun x hx => ?_)
      show R.orient x (exteriorDerivative b x) = R.orient x (exteriorDerivative γ x)
      rw [hloc x hx]
    have hle := hE1 P m U (ball 0 s) A.boundary ⟨γ, hγU⟩ 1 hAfin hγsupp hγnorm
    rw [hkey, one_mul] at *
    calc ENNReal.ofReal (A.boundary ⟨γ, hγU⟩)
        ≤ ENNReal.ofReal (A.boundary.massOn (ball 0 s)).toReal :=
          ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hle)
      _ = A.boundary.massOn (ball 0 s) := ENNReal.ofReal_toReal hAfin
  exact ⟨Ŝ, R', hR'rep, hR'meas, hagree, hbdry, hmass⟩
```

## Key steps

1. (IMC)(b) restricts R to M ∩ B_ρ in U; the same data form an IMRep in ℝ^P (local integrability from the compact closedBall(0, ρ) ⊆ U), and (IMC)(b) in ℝ^P gives the represented current Ŝ.
2. (RS)(c): R′.measure = μ⌞B_ρ and Ŝ(ω) = ∫_{B_ρ} ⟨ω, ξ⟩ dμ for every test form ω.
3. Forms supported in B_ρ vanish off B_ρ, so Ŝ(ω) = ∫ ⟨ω, ξ⟩ dμ = S(ω) = currentEval(S, ω); with tsupport dβ ⊆ tsupport β this gives ∂Ŝ(β) = ∂S(β) = 0 inside B_ρ.
4. For |β| ≤ 1 and a smooth bump χ (χ = 1 near closedBall(0, ρ), tsupport χ ⊆ B_s): ∂Ŝ(β) = ∫_{B_ρ} ⟨d(χβ), ξ⟩ dμ = ∂A(χβ), and (E1) bounds it by M_{B_s}(∂A); take the supremum.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `python3 scans of RUN/dag.json: selected node, parent root.dimension_reduction_results-a1.moving_blowups-a1 and its children, dependency types (dor_imrep_massOn_eq_measure_and_support, dimred_mbl_current_foundations, dimred_mbl_slice_mass_bounds, dimred_mbl_closure_and_boundary_rectifiability), accepted declarations mentioning massOn/IMRep/compact/diagonal/separab, collisions for dimred_mbl_tc_*`
- `rg -n 'Banach|Alaoglu|SecondCountableTopology|IsSeparable|diagonal|extraction' lake-packages/simongmt/Poincare/SimonGMT/Chapter06 (no match); rg -n 'WeaklyConvergesOn|Banach' SNAPSHOT/project --glob '*.lean'`
- `rg -n 'instSecondCountableTopology|theorem extraction_forall_of_eventually|IsSeparable.exists_countable_dense_subset|Filter.EventuallyEq.extDeriv_eq' SNAPSHOT/mathlib/Mathlib; grep of setLIntegral_congr_fun, lipschitzWith_one_norm, ContDiffBump API, tsupport_sub, norm_iteratedFDeriv_zero`
- `sed -n on book/chapter-06.txt lines 284–333 (2.9, 2.13–2.15), 755–767 (3.2), 875–895 (3.11), 1330–1380 (4.6–4.10)`
- `grep -n _existing_lean_name_problem _overlay_accepted_children _accepted_checkpoint ensure in /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py and store.py; contract_scope in verifier/gmt-compare.py`
- `lake env lean on Types/Final.lean (7 child types), Assembly.lean (conditional parent), LT.lean, TR.lean, WC.lean (child proofs from sibling types), SubForm.lean and SubParent.lean (Submission-form compile), all with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-truncated-compactness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-eva-463e096c91/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-cov-64249b6f60/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-imrep-1bd5f15878/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/tmp/tc-decomp-x7k2/lean/Assembly.lean`
- `/tmp/tc-decomp-x7k2/lean/TR.lean`
- `/tmp/tc-decomp-x7k2/lean/WC.lean`
- `/tmp/tc-decomp-x7k2/lean/LT.lean`

Pins match: HEAD b4d606d, Mathlib 25730c7c, SimonGMT 2b366308, and Submission.lean is byte-identical to Contract.lean. Neither the pinned libraries nor any accepted DAG node proves weak compactness of currents. SimonGMT Chapter06 has no match. The project snapshot states Simon 2.15 only as the unproved Ch06 contract conjunct CompactnessUnderMassBounds (GMT/Ch06/Contract.lean:194–205), a different problem. So weak_compactness is a new child. Its Lean route exists in Mathlib: ContinuousMap.instSecondCountableTopology (separate import), IsSeparable.exists_countable_dense_subset, IsCompact.tendsto_subseq on a countable product, and norm_iteratedFDeriv_zero. The cut-off uses ContDiffBump and Filter.EventuallyEq.extDeriv_eq. Step 1 uses Filter.extraction_forall_of_eventually. Four accepted declarations are reused with identical frozen types: cmr_abs_apply_le_massOn, cmr_covector_euclidean_equiv, cmc_imRep_locality_restrict_sub and lcmp_imRep_measure_restrict. The new names dimred_mbl_tc_* collide with nothing. All child types elaborate. The conditional assembly proves the exact parent type, and each new child is proved in Lean from its sibling types. All of these depend only on propext, Classical.choice and Quot.sound.
