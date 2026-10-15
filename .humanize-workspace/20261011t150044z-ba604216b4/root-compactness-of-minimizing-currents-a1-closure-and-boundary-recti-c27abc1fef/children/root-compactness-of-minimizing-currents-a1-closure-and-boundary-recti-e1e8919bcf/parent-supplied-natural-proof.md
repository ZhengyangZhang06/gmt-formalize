# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.null_off_image-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.null_off_image-a1.setintegral_eq_preimage-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1, 2 and 4 of the parent proof (σ₁, σ₂ built from u^± Lⁿ⌞U and q_*(h^∓σ), equality of their test integrals, uniqueness), evaluated on a measurable B ⊆ U. Measurable representatives (parent step 0) are not needed here, because the withDensity lemmas below only require a.e.-measurable densities. Finiteness of σ is not used: the push-forward measures are finite because h is integrable.
1. (Four finite measures.) Write ofReal : ℝ → [0,∞]; recall ofReal(t) = ofReal(max(t, 0)) and (ofReal t).toReal = max(t, 0) (ENNReal.toReal_ofReal'). Define:
- λ₊ := (Lⁿ⌞U).withDensity(y ↦ ofReal(u y)) and λ₋ := (Lⁿ⌞U).withDensity(y ↦ ofReal(−u y));
- m₊ := q_*(σ.withDensity(x ↦ ofReal(h x))) and m₋ := q_*(σ.withDensity(x ↦ ofReal(−h x))), where q_* = Measure.map q.
These are u⁺Lⁿ⌞U, u⁻Lⁿ⌞U, q_*(h⁺σ) and q_*(h⁻σ). Since u and −u have finite integral for Lⁿ⌞U, and h and −h have finite σ-integral, the four withDensity measures are finite (isFiniteMeasure_withDensity_ofReal). Push-forwards of finite measures are finite (Measure.isFiniteMeasure_map). Put μ₁ := λ₊ + m₋ and μ₂ := λ₋ + m₊; both are finite measures on ℝⁿ.
2. (Integrals against these measures.)
(a) If f is integrable on U, then for every b : ℝⁿ → ℝ, ∫ b d((Lⁿ⌞U).withDensity(ofReal ∘ f)) = ∫_U max(f(y), 0) b(y) dy. Indeed, the density ofReal ∘ f is a.e.-measurable for Lⁿ⌞U (f is a.e.-strongly measurable) and everywhere finite, so integral_withDensity_eq_integral_toReal_smul₀ applies, and (ofReal f(y)).toReal = max(f(y), 0).
(b) If g is σ-integrable and b is continuous, then ∫ b d(q_*(σ.withDensity(ofReal ∘ g))) = ∫ b(q x) d(σ.withDensity(ofReal ∘ g))(x) (integral_map: q is measurable, and b, being continuous, is a.e.-strongly measurable). By the same withDensity lemma this equals ∫ max(g(x), 0) b(q(x)) dσ(x).
3. (Equal integrals of test functions.) Let b : ℝⁿ → ℝ be ContDiff ℝ (⊤ : ℕ∞) with compact support and tsupport b ⊆ U. Then b is continuous with compact support, hence bounded, |b| ≤ C (Continuous.bounded_above_of_compact_support), and integrable for every finite measure (Continuous.integrable_of_hasCompactSupport). By integral_add_measure and step 2 (with f = u, −u and g = h, −h):
- ∫ b dμ₁ = ∫_U max(u, 0) b dy + ∫ max(−h, 0)·(b∘q) dσ;
- ∫ b dμ₂ = ∫_U max(−u, 0) b dy + ∫ max(h, 0)·(b∘q) dσ.
The integrands are integrable: max(±u, 0) is Lⁿ⌞U-integrable (Integrable.pos_part / Integrable.neg_part) and b is bounded and measurable (Integrable.mul_bdd); likewise max(±h, 0)·(b∘q) is σ-integrable, since b∘q is bounded and measurable. Since max(t, 0) − max(−t, 0) = t (max_zero_sub_max_neg_zero_eq_self), integral_sub gives:
- ∫_U max(u, 0) b − ∫_U max(−u, 0) b = ∫_U b u;
- ∫ max(h, 0)(b∘q) dσ − ∫ max(−h, 0)(b∘q) dσ = ∫ (b∘q) h dσ.
By hypothesis ∫_U b u = ∫ (b∘q) h dσ. Combining these four real identities linearly, ∫ b dμ₁ − ∫ b dμ₂ = ∫_U b u − ∫ (b∘q) h dσ = 0, i.e. ∫ b dμ₁ = ∫ b dμ₂.
4. (Uniqueness on U.) By the sibling theorem Submission.cbr_ci_pw_noi_restrict_eq_of_smooth_test (U open, μ₁ and μ₂ finite, step 3), μ₁⌞U = μ₂⌞U. Let B ⊆ U be measurable. Then μ_i(B) = μ_i(B ∩ U) = (μ_i⌞U)(B) (Measure.restrict_apply, B ∩ U = B). Hence λ₊(B) + m₋(B) = λ₋(B) + m₊(B) (Measure.add_apply), an identity between finite numbers.
5. (Evaluation on B.) For measurable B ⊆ U:
- λ_±(B) = ∫⁻_B ofReal(±u) dLⁿ (withDensity_apply, then Measure.restrict_restrict: (Lⁿ⌞U)⌞B = Lⁿ⌞(B ∩ U) = Lⁿ⌞B);
- m_±(B) = σ.withDensity(ofReal ∘ (±h))(q⁻¹B) = ∫⁻_{q⁻¹B} ofReal(±h) dσ (Measure.map_apply with q and B measurable, then withDensity_apply with q⁻¹B measurable).
6. (Conclusion.) u is integrable on B (as B ⊆ U) and h is integrable on q⁻¹B. So by integral_eq_lintegral_pos_part_sub_lintegral_neg_part and step 5:
- ∫_B u dy = λ₊(B).toReal − λ₋(B).toReal;
- ∫_{q⁻¹B} h dσ = m₊(B).toReal − m₋(B).toReal.
Applying toReal to the identity of step 4 (ENNReal.toReal_add, all four values finite by measure_ne_top) gives λ₊(B).toReal + m₋(B).toReal = λ₋(B).toReal + m₊(B).toReal. Therefore ∫_B u dy = λ₊(B).toReal − λ₋(B).toReal = m₊(B).toReal − m₋(B).toReal = ∫_{q⁻¹B} h dσ. ∎

Formalization note: in Lean, `∫ y in U, f y - ∫ y in U, g y` parses with the subtraction inside the first integrand, because the integrand is parsed at precedence 60 and `-` has precedence 65. Write `(∫ y in U, f y) - ∫ y in U, g y` instead. The frozen type `∫ y in B, u y = ∫ x in q ⁻¹' B, h x ∂σ` is unaffected because `=` has precedence 50.

Appendix (reference only): a Lean script of exactly this argument. It was checked with `lake env lean` after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the frozen contract's `open`s (project b4d606db, Mathlib 25730c7c), inserted before `main_theorem` and after the sibling theorems. It compiles without `sorry` and uses only the axioms propext, Classical.choice and Quot.sound.
```lean
theorem Submission.cbr_ci_pw_noi_setIntegral_eq_preimage : ∀ (P n : ℕ) (U : Set (Euclid n)) (u : Euclid n → ℝ) (σ : Measure (Euclid P)) (q : Euclid P → Euclid n) (h : Euclid P → ℝ), IsOpen U → Measurable q → IntegrableOn u U → Integrable h σ → (∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → ∫ y in U, b y * u y = ∫ x, b (q x) * h x ∂σ) → ∀ B : Set (Euclid n), MeasurableSet B → B ⊆ U → ∫ y in B, u y = ∫ x in q ⁻¹' B, h x ∂σ := by
  intro P n U u σ q h hU hq hu hh htest B hB hBU
  -- the four finite measures `λ±` and `m±`
  set lp : Measure (Euclid n) := (volume.restrict U).withDensity fun y => ENNReal.ofReal (u y)
    with hlp
  set lm : Measure (Euclid n) := (volume.restrict U).withDensity fun y => ENNReal.ofReal (-u y)
    with hlm
  set mp : Measure (Euclid n) := (σ.withDensity fun x => ENNReal.ofReal (h x)).map q with hmp
  set mm : Measure (Euclid n) := (σ.withDensity fun x => ENNReal.ofReal (-h x)).map q with hmm
  have hlpf : IsFiniteMeasure lp := isFiniteMeasure_withDensity_ofReal hu.2
  have hlmf : IsFiniteMeasure lm := isFiniteMeasure_withDensity_ofReal hu.neg.2
  have hmpf : IsFiniteMeasure mp := by
    have : IsFiniteMeasure (σ.withDensity fun x => ENNReal.ofReal (h x)) :=
      isFiniteMeasure_withDensity_ofReal hh.2
    exact Measure.isFiniteMeasure_map _ _
  have hmmf : IsFiniteMeasure mm := by
    have : IsFiniteMeasure (σ.withDensity fun x => ENNReal.ofReal (-h x)) :=
      isFiniteMeasure_withDensity_ofReal hh.neg.2
    exact Measure.isFiniteMeasure_map _ _
  -- integrals of a test function against `λ±` and `m±`
  have hlam : ∀ (f : Euclid n → ℝ) (b : Euclid n → ℝ), IntegrableOn f U →
      ∫ y, b y ∂((volume.restrict U).withDensity fun y => ENNReal.ofReal (f y)) =
        ∫ y in U, max (f y) 0 * b y := by
    intro f b hf
    rw [integral_withDensity_eq_integral_toReal_smul₀ hf.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  have hpush : ∀ (g : Euclid P → ℝ) (b : Euclid n → ℝ), Integrable g σ → Continuous b →
      ∫ y, b y ∂((σ.withDensity fun x => ENNReal.ofReal (g x)).map q) =
        ∫ x, max (g x) 0 * b (q x) ∂σ := by
    intro g b hg hb
    rw [integral_map hq.aemeasurable hb.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul₀ hg.aemeasurable.ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  -- equal integrals of test functions
  have hkey : ∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U →
      ∫ y, b y ∂(lp + mm) = ∫ y, b y ∂(lm + mp) := by
    intro b hb hbc hbU
    have hbcont : Continuous b := hb.continuous
    obtain ⟨C, hC⟩ := hbcont.bounded_above_of_compact_support hbc
    have hbm : AEStronglyMeasurable b (volume.restrict U) := hbcont.aestronglyMeasurable
    have hbqm : AEStronglyMeasurable (fun x => b (q x)) σ :=
      (hbcont.measurable.comp hq).aestronglyMeasurable
    rw [integral_add_measure (hbcont.integrable_of_hasCompactSupport hbc)
        (hbcont.integrable_of_hasCompactSupport hbc),
      integral_add_measure (hbcont.integrable_of_hasCompactSupport hbc)
        (hbcont.integrable_of_hasCompactSupport hbc),
      hlam u b hu, hlam (fun y => -u y) b hu.neg, hpush h b hh hbcont,
      hpush (fun x => -h x) b hh.neg hbcont]
    have I1 : (∫ y in U, max (u y) 0 * b y) - ∫ y in U, max (-u y) 0 * b y =
        ∫ y in U, b y * u y := by
      have hsub := integral_sub (hu.pos_part.mul_bdd hbm (Eventually.of_forall hC))
        (hu.neg_part.mul_bdd hbm (Eventually.of_forall hC))
      refine hsub.symm.trans (integral_congr_ae (Eventually.of_forall fun y => ?_))
      simp only
      rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self, mul_comm]
    have I2 : ∫ x, max (h x) 0 * b (q x) ∂σ - ∫ x, max (-h x) 0 * b (q x) ∂σ =
        ∫ x, b (q x) * h x ∂σ := by
      have hsub := integral_sub (hh.pos_part.mul_bdd hbqm (Eventually.of_forall fun x => hC (q x)))
        (hh.neg_part.mul_bdd hbqm (Eventually.of_forall fun x => hC (q x)))
      refine hsub.symm.trans (integral_congr_ae (Eventually.of_forall fun x => ?_))
      simp only
      rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self, mul_comm]
    have := htest b hb hbc hbU
    linarith
  -- uniqueness: the two measures agree on subsets of `U`
  have hres := Submission.cbr_ci_pw_noi_restrict_eq_of_smooth_test n U (lp + mm) (lm + mp) hU
    inferInstance inferInstance hkey
  have hBeq : (lp + mm) B = (lm + mp) B := by
    have := congrArg (fun μ : Measure (Euclid n) => μ B) hres
    simpa only [Measure.restrict_apply hB, inter_eq_left.mpr hBU] using this
  -- evaluate the four measures on `B`
  have hlB : ∀ f : Euclid n → ℝ, ((volume.restrict U).withDensity fun y => ENNReal.ofReal (f y)) B =
      ∫⁻ y in B, ENNReal.ofReal (f y) := by
    intro f
    rw [withDensity_apply _ hB, Measure.restrict_restrict hB, inter_eq_left.mpr hBU]
  have hmB : ∀ g : Euclid P → ℝ, ((σ.withDensity fun x => ENNReal.ofReal (g x)).map q) B =
      ∫⁻ x in q ⁻¹' B, ENNReal.ofReal (g x) ∂σ := by
    intro g
    rw [Measure.map_apply hq hB, withDensity_apply _ (hq hB)]
  rw [Measure.add_apply, Measure.add_apply] at hBeq
  have hreal : (lp B).toReal + (mm B).toReal = (lm B).toReal + (mp B).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hBeq]
  -- convert to real integrals
  have hL : ∫ y in B, u y = (lp B).toReal - (lm B).toReal := by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hu.mono_set hBU), hlp, hlm, hlB, hlB]
  have hR : ∫ x in q ⁻¹' B, h x ∂σ = (mp B).toReal - (mm B).toReal := by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hh.integrableOn, hmp, hmm, hmB, hmB]
  rw [hL, hR]
  linarith
```

## Key steps

1. λ± := (Lⁿ⌞U).withDensity(ofReal(±u)) and m± := q_*(σ.withDensity(ofReal(±h))) are finite measures; set μ₁ := λ₊ + m₋ and μ₂ := λ₋ + m₊.
2. For smooth compactly supported b with tsupport b ⊆ U: ∫ b dμ₁ − ∫ b dμ₂ = ∫_U b u − ∫ (b∘q) h dσ = 0 (withDensity and map integral formulas, u = u⁺ − u⁻, h = h⁺ − h⁻).
3. The sibling uniqueness lemma gives μ₁⌞U = μ₂⌞U, so λ₊(B) + m₋(B) = λ₋(B) + m₊(B) for measurable B ⊆ U.
4. λ±(B) = ∫⁻_B ofReal(±u) and m±(B) = ∫⁻_{q⁻¹B} ofReal(±h) dσ; writing each integral as positive part minus negative part yields ∫_B u = ∫_{q⁻¹B} h dσ.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git show b1f7ad57dc2d4b5bf68702805f4f51beebe5d575:GMT/Ch07/Submission.lean (proof base = frozen contract only, 457 lines, no helper declarations)`
- `python3 -I scans of dag.json: lean_name prefix cbr_ci_pw (17 existing names; cbr_ci_pw_noi_smooth_cutoff_seq, cbr_ci_pw_noi_restrict_eq_of_smooth_test, cbr_ci_pw_noi_setIntegral_eq_preimage each occur 0 times); accepted lean_statements containing Measure+HasCompactSupport+ContDiff or withDensity/toMeasurable/'μ G = ν G' (found rsd_mw_tfa_smooth_cutoff, cmc_ml_measure_eq_of_eq_on_open_subsets, cbr_setIntegral_eq_of_integral_eq, rsd_ae_tendsto_withDensity_div_closedBall; none has a needed type)`
- `rg -n in local-references/123e8435b4a2469b/mathlib/Mathlib: 'theorem exists_contDiff_support_eq_eq_one_iff' (Geometry/Manifold/PartitionOfUnity.lean:789), 'exists_cthickening_subset_open' (Topology/MetricSpace/Thickening.lean:426), 'IsCompact.cthickening' (Thickening.lean:283), "theorem cthickening_subset_thickening'" (Thickening.lean:261), 'theorem closure_thickening_subset_cthickening' (:293), 'theorem self_subset_cthickening' (:313), 'theorem continuous_infEDist' / 'theorem infEDist_zero_of_mem' / 'theorem infEDist_pos_iff_notMem_closure' (Topology/MetricSpace/HausdorffDistance.lean:140/107/174, namespace Metric, capital-D infEDist), 'theorem tendsto_inv_nat_nhds_zero' (Topology/Instances/ENNReal/Lemmas.lean:486)`
- `rg -n in the snapshot Mathlib: 'theorem tendsto_integral_of_dominated_convergence' (MeasureTheory/Integral/DominatedConvergence.lean:57), 'theorem integral_indicator_one' (Integral/Bochner/Set.lean:533), 'theorem ext_of_generate_finite' (Measure/Typeclasses/Finite.lean:458), 'theorem isPiSystem_isOpen' (Constructions/BorelSpace/Basic.lean:81), 'class BorelSpace' (BorelSpace/Basic.lean:113), 'theorem integral_withDensity_eq_integral_toReal_smul₀' (Integral/Bochner/ContinuousLinearMap.lean:311, root namespace), 'theorem isFiniteMeasure_withDensity_ofReal' (Function/L1Space/HasFiniteIntegral.lean:310), 'Measure.isFiniteMeasure_map' (Measure/Typeclasses/Finite.lean:124), 'theorem integral_map ' (Integral/Bochner/Basic.lean:1081), 'theorem integral_add_measure' (Bochner/Basic.lean:1012), 'theorem integral_sub ' (Bochner/Basic.lean:263)`
- `rg -n in the snapshot Mathlib: 'Continuous.integrable_of_hasCompactSupport' (Function/LocallyIntegrable.lean:622), 'Continuous.bounded_above_of_compact_support' (Analysis/Normed/Group/Bounded.lean:153), 'theorem Integrable.mul_bdd' / 'theorem Integrable.pos_part' (Function/L1Space/Integrable.lean:1072/948), 'max_zero_sub_max_neg_zero_eq_self' (Algebra/Order/Group/MinMax.lean, to_additive), "theorem toReal_ofReal'" (Basic/ENNReal/Basic.lean:255), "toReal_eq_toReal_iff'" (Basic/ENNReal/Basic.lean:431), 'theorem toReal_add ' (Basic/ENNReal/Real.lean:41), 'theorem integral_eq_lintegral_pos_part_sub_lintegral_neg_part' (Bochner/Basic.lean:486), 'theorem withDensity_apply ' (Measure/WithDensity.lean:44), 'theorem map_apply (hf : Measurable f)' (Measure/Map.lean:170), 'theorem restrict_restrict (hs' (Measure/Restrict.lean:205), 'theorem measure_toMeasurable_inter_of_sFinite' (Typeclasses/SFinite.lean:477), 'theorem integral_eq_zero_iff_of_nonneg_ae' (Bochner/Basic.lean:763), 'theorem ae_restrict_of_ae_restrict_of_subset' (Measure/Restrict.lean:654)`
- `rg -n 'theorem ext_of_forall_integral_eq|theorem ext_of_integral|ext_of_integral_eq_on_compactlySupported|ae_eq_zero_of_integral_contDiff_smul_eq_zero' in the snapshot Mathlib (RieszMarkovKakutani/Real.lean:412 needs equal integrals for all of C_c(X, ℝ) and regular measures; Analysis/Distribution/AEEqOfIntegralContDiff.lean:205 concerns one locally integrable function, not a push-forward measure; HasOuterApproxClosed.lean:269 needs all bounded continuous functions)`
- `lake env lean /tmp/noi-decomp/T0.lean, T2.lean, T3.lean (#check reachability after import GMT.Ch07.Submission; instance check IsFiniteMeasure → IsFiniteMeasureOnCompacts)`
- `lake env lean /tmp/noi-decomp/C1.lean (child 1 fully proved), C2.lean (child 2 from child 1), C3.lean (child 3 from child 2), Asm.lean and Full.lean (all four theorems, no sorry; #print axioms → propext, Classical.choice, Quot.sound), SubTest.lean (the four theorems inserted into a copy of GMT/Ch07/Submission.lean before main_theorem; only the frozen main_theorem sorry remains)`
- `python3 -I validate_lean_statement from verifier/lean_contract.py on the three child types (pass); regex replica of leaf_verification.check_source_delta forbidden-token test on each proof body (no match)`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose: node depth 5 < max_depth 6; _existing_lean_name_problem; _install_parent_supplied_child_handoff), leaf_verification.py check_source_delta, prompts.py DECOMPOSE / DECOMPOSITION_AUDIT / RLCR_LEAN_TASK`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-c27abc1fef/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-c27abc1fef/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Group/MinMax.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/prompts.py`
- `/tmp/noi-decomp/C1.lean`
- `/tmp/noi-decomp/C2.lean`
- `/tmp/noi-decomp/C3.lean`
- `/tmp/noi-decomp/Asm.lean`
- `/tmp/noi-decomp/Full.lean`
- `/tmp/noi-decomp/SubTest.lean`

The snapshot (project b4d606db, Mathlib 25730c7c) contract equals the workspace Contract.lean and Submission.lean, and proof base b1f7ad57 adds no helper declarations. Every Mathlib lemma cited in the three child proofs exists in the snapshot under the cited name (note Metric.infEDist with a capital D and the root-namespace integral_withDensity_eq_integral_toReal_smul₀) and is reachable from import GMT.Ch07.Submission. No Mathlib or DAG declaration has the exact child types: Measure.ext_of_integral_eq_on_compactlySupported needs all C_c(X) tests and regular measures; IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero concerns a single locally integrable function, not a push-forward; and the accepted cmc_ml_measure_eq_of_eq_on_open_subsets and rsd_mw_tfa_smooth_cutoff have different types. The three proposed names are absent from dag.json. All child types elaborate in the contract scope and pass validate_lean_statement. Complete Lean proofs of the three children, and of the frozen parent from child 3 alone, compile in a copy of Submission.lean with standard axioms only, and the forbidden-token check is clean.
