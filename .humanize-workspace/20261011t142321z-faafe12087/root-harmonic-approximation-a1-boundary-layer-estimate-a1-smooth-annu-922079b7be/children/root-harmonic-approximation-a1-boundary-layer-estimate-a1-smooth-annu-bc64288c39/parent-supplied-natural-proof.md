# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1.boundary_layer_estimate-a1.smooth_annulus_estimate-a1`
- Child DAG node: `root.harmonic_approximation-a1.boundary_layer_estimate-a1.smooth_annulus_estimate-a1.dilation_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source and role. This is step 1 ("Dilation formula") of the supplied proof of ble_smooth_annulus_estimate. Here the dilated set tE is written as the preimage E_t := {y : t⁻¹ • y ∈ E}, because the frozen contract does not open `Pointwise` and so `t • E` cannot be written. For t ≠ 0 the two sets agree: y ∈ tE ⟺ y = t x with x ∈ E ⟺ t⁻¹ y ∈ E. The parent uses this lemma in its step 4 (gradient term). The sibling annulus_kernel_bound uses it in its step 2.

Notation. R^n is Rn n = EuclideanSpace ℝ (Fin n), with Lebesgue measure `volume`. This is an additive Haar measure, and finrank ℝ (Rn n) = n (finrank_euclideanSpace_fin). All integrals are lintegrals with values in [0, ∞]. The factor t^{-n} enters as ENNReal.ofReal ((t ^ n)⁻¹).

Hypotheses: n ∈ ℕ; F : R^n → [0, ∞] is arbitrary (no measurability is assumed); E ⊆ R^n is arbitrary (no measurability is assumed); t ∈ ℝ with t > 0.
Claim: ∫_E F(t x) dx = t^{-n} ∫_{E_t} F(y) dy, where E_t := {y : t⁻¹ y ∈ E}.

Proof.

1. The dilation is a measurable equivalence. Since t ≠ 0, the map T(x) := t x is a homeomorphism of R^n with inverse y ↦ t⁻¹ y. Hence it is a measurable equivalence e : R^n ≃ᵐ R^n with e x = t x for all x. In Lean, e := (Homeomorph.smul (Units.mk0 t ht.ne')).toMeasurableEquiv, and e x = t • x holds by rfl.

2. Preimage. e⁻¹(E_t) = {x : t⁻¹(t x) ∈ E} = {x : x ∈ E} = E, because t⁻¹(t x) = (t⁻¹ t) x = x (smul_smul, inv_mul_cancel₀, one_smul).

3. Pushforward of Lebesgue measure. Measure.map_addHaar_smul applies to the additive Haar measure volume and t ≠ 0. It gives map (t • ·) volume = ENNReal.ofReal |(t^{finrank ℝ (Rn n)})⁻¹| • volume. Since finrank ℝ (Rn n) = n and t > 0, we have |(t^n)⁻¹| = (t^n)⁻¹. Hence map e volume = ENNReal.ofReal ((t^n)⁻¹) • volume.

4. Change of variables along a measurable embedding. A measurable equivalence is a measurable embedding. For a measurable embedding e, every set S ⊆ R^n and every g : R^n → [0, ∞], no measurability is needed:
   - (map e volume).restrict S = map e (volume.restrict (e⁻¹ S)) (MeasurableEmbedding.restrict_map);
   - ∫ g d(map e ν) = ∫ (g ∘ e) dν (MeasurableEmbedding.lintegral_map).
Therefore ∫_{e⁻¹(S)} F(e x) dx = ∫_S F d(map e volume).

5. Conclusion. By step 2, then step 4 with S = E_t, then step 3:
∫_E F(t x) dx = ∫_{e⁻¹(E_t)} F(e x) dx = ∫_{E_t} F d(map e volume) = ∫_{E_t} F d(ENNReal.ofReal((t^n)⁻¹) • volume) = ENNReal.ofReal((t^n)⁻¹) ∫_{E_t} F(y) dy.
The last equality uses Measure.restrict_smul (restricting a scalar multiple of a measure) and lintegral_smul_measure (a scalar multiple of the measure comes out of the lintegral). QED.

Formalization note. The following proof of this exact frozen statement compiles against the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c) after `import GMT.Ch05.Submission`, inside `namespace GMT.Ch05` / `namespace Submission` with the contract's `open`s. No extra imports or helpers are needed. `#print axioms` lists only propext, Classical.choice and Quot.sound. A copy is in the git-ignored GMT/Scratch/ble_sac/ble_sac_lintegral_comp_smul.lean.txt.

```lean
theorem ble_sac_lintegral_comp_smul : ∀ (n : ℕ) (F : Rn n → ℝ≥0∞) (E : Set (Rn n)) (t : ℝ), 0 < t → ∫⁻ x in E, F (t • x) = ENNReal.ofReal ((t ^ n)⁻¹) * ∫⁻ y in (fun y => t⁻¹ • y) ⁻¹' E, F y := by
  intro n F E t ht
  let e : Rn n ≃ᵐ Rn n := (Homeomorph.smul (Units.mk0 t ht.ne')).toMeasurableEquiv
  have he : ∀ x, e x = t • x := fun x => rfl
  have hpre : e ⁻¹' ((fun y => t⁻¹ • y) ⁻¹' E) = E := by
    ext x
    simp only [mem_preimage, he, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  have hmap : Measure.map e volume = ENNReal.ofReal ((t ^ n)⁻¹) • (volume : Measure (Rn n)) := by
    have := Measure.map_addHaar_smul (volume : Measure (Rn n)) ht.ne'
    rw [finrank_euclideanSpace_fin] at this
    rw [show (e : Rn n → Rn n) = fun x => t • x from funext he, this]
    congr 2
    rw [abs_of_pos (by positivity)]
  calc ∫⁻ x in E, F (t • x) = ∫⁻ x in e ⁻¹' ((fun y => t⁻¹ • y) ⁻¹' E), F (e x) := by
        rw [hpre]; simp only [he]
    _ = ∫⁻ y in (fun y => t⁻¹ • y) ⁻¹' E, F y ∂(Measure.map e volume) := by
        rw [e.measurableEmbedding.restrict_map, e.measurableEmbedding.lintegral_map]
    _ = _ := by rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
```

## Key steps

1. x ↦ t x is a measurable equivalence e (Homeomorph.smul (Units.mk0 t _)) with e⁻¹(E_t) = E
2. map e volume = ENNReal.ofReal((t^n)⁻¹) • volume by Measure.map_addHaar_smul and finrank_euclideanSpace_fin = n
3. change of variables along the measurable embedding e (restrict_map, lintegral_map), valid for arbitrary F and E
4. pull the scalar out of the restricted scaled measure (Measure.restrict_smul, lintegral_smul_measure)

## Reference use

### local-project

Queries:
- `cmp /tmp/sac-decomp/proj/GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Submission.lean (SAME_AS_SNAPSHOT); sha256sum Contract.lean Submission.lean (both c966f51efddb5a68ce15ef2a2a322fd9df0ca69da4626c7acef05b05d1691e12)`
- `rg -n "theorem (setLIntegral_mono|setLIntegral_mono'|lintegral_const_mul'|lintegral_const_mul|setLIntegral_const|lintegral_mono_set|lintegral_add_left|lintegral_add_right|setLIntegral_congr_fun)\b" <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/`
- `rg -n "theorem (lintegral_lintegral_swap|Measurable.lintegral_prod_right'|Measurable.lintegral_prod_right|lintegral_prod_swap)\b" <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `rg -n "theorem map_addHaar_smul|theorem addHaar_smul\b|theorem addHaar_preimage_smul" .../Measure/Lebesgue/EqHaar.lean; rg -n "theorem volume_Icc|theorem volume_Ioc" .../Measure/Lebesgue/Basic.lean`
- `rg -n "theorem (lintegral_comp_smul|setLIntegral_comp_smul|lintegral_comp_smul_deriv|lintegral_comp_mul_left)" <snapshot>/mathlib/Mathlib/MeasureTheory/  (no match)`
- `grep -rn "mul_le_mul_iff_right|ofReal_ofNat|ofReal_eq_zero" <snapshot>/mathlib/Mathlib/Basic/ENNReal/*.lean  (Data/ENNReal/*.lean are 5-line deprecated stubs re-exporting Mathlib.Basic.ENNReal.*)`
- `grep -n for enorm_integral_le_lintegral_enorm, integral_eq_sub_of_hasDerivAt, inner_gradient_left, toDual_symm_apply, lintegral_mul_le_Lp_mul_Lq, HolderConjugate two_two, add_sq_le, two_mul_le_add_sq, enorm_le_iff_norm_le, ofReal_norm, norm_inner_le_norm, ENNReal.rpow_two/rpow_natCast/rpow_mul, ENNReal.continuous_pow, ContDiff.continuous_fderiv, Continuous.enorm, integral_of_le, norm_integral_le_integral_norm, integral_mono_interval`
- `grep -n for lintegral_indicator, lintegral_indicator_const, setLIntegral_le_lintegral, lintegral_smul_measure, lintegral_mul_const, restrict_map, lintegral_map, finrank_euclideanSpace_fin, measurable_prodMk_right, restrict_smul`
- `python scan of dag.json lean_name fields and lean_statements plus all nodes/*/* files for 'ble_sac_' (none); grep -rl ble_sac GMT/ and <snapshot>/project (none); git grep -l -e ble_sac_ across all 614 refs, *.lean (none)`
- `lake env lean Check/{Types,All,Three,Ray,Kern,Full,SubShaped,Statements,FromPaste,SplitAllFinal,SubShapedFinal}.lean in scratch project /tmp/sac-decomp/proj (frozen Submission compiled to an olean); #print axioms on all four declarations`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Data/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/Real/ConjExponents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Order/Ring/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Order/Ring/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-boundary-layer-estimate-a1-smooth-annu-922079b7be/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-boundary-layer-estimate-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/ble_sac/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/ble_sac/ble_sac_split_all.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/ble_sac/check_submission_shaped.lean.txt`
- `/tmp/sac-decomp/proj/Check/Full.lean`
- `/tmp/sac-decomp/proj/Check/SubShaped.lean`

Pinned snapshot: project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). The frozen Submission.lean is byte-identical in the snapshot, the workspace and the scratch project, with SHA-256 c966f51e….

No match in the snapshot (gaps the children fill):
- There is no lintegral dilation lemma: lintegral_comp_smul and setLIntegral_comp_smul do not exist under MeasureTheory. Child dilation_formula provides it from Measure.map_addHaar_smul (Lebesgue/EqHaar.lean:336), finrank_euclideanSpace_fin (PiL2.lean:205), MeasurableEmbedding.restrict_map and lintegral_map, Measure.restrict_smul (Restrict.lean:193) and lintegral_smul_measure (Lebesgue/Basic.lean:418).
- There is no ray, Cauchy–Schwarz or annulus-kernel lemma either.

Usable lemmas, all verified to exist and used in the compiled proofs:
- Set integrals: setLIntegral_mono and setLIntegral_mono' (Lebesgue/Basic.lean:246,254), setLIntegral_const (:121), lintegral_mono_set (:98), setLIntegral_congr_fun (:298), setLIntegral_le_lintegral (:258), lintegral_indicator (:510), lintegral_indicator_const (:541).
- Linearity: lintegral_add_left and lintegral_add_right (Lebesgue/Add.lean:316,339), lintegral_const_mul and lintegral_const_mul' (:381,420), lintegral_mul_const (:433).
- Tonelli: Measurable.lintegral_prod_right' and lintegral_lintegral_swap (Measure/Prod.lean:123,1071).
- Lebesgue measure on ℝ: Real.volume_Icc and volume_Ioc (Lebesgue/Basic.lean:86,110).
- Integral bounds: ENNReal.lintegral_mul_le_Lp_mul_Lq (MeanInequalities.lean:202), Real.HolderConjugate.two_two (Basic/Real/ConjExponents.lean:137), enorm_integral_le_lintegral_enorm (Bochner/Basic.lean:333).
- Calculus: intervalIntegral.integral_eq_sub_of_hasDerivAt (FundThmCalculus.lean:1148), intervalIntegral.integral_of_le (IntervalIntegral/Basic.lean:677), inner_gradient_left (Gradient/Basic.lean:292), ContDiff.continuous_fderiv (ContDiff/Defs.lean:1271; takes n ≠ 0).
- Norms and inner products: enorm_le_iff_norm_le (Normed/Group/Basic.lean:399), norm_inner_le_norm (InnerProductSpace/Basic.lean:455), add_sq_le (Algebra/Order/Ring/Basic.lean:113).
- ENNReal: ENNReal.mul_le_mul_iff_right (Basic/ENNReal/Operations.lean:75), ENNReal.ofReal_ofNat (Basic/ENNReal/Basic.lean:512), ENNReal.ofReal_eq_zero (Basic/ENNReal/Real.lean:181), ENNReal.continuous_pow (Topology/Instances/ENNReal/Lemmas.lean:406), ENNReal.rpow_two, rpow_natCast and rpow_mul (Pow/NNReal.lean:701,686,669).

API drift found: Data/ENNReal/* are deprecated stubs pointing to Mathlib.Basic.ENNReal.*; Set.mem_diff, Set.mem_setOf_eq and Set.diff_subset are deprecated in favor of Set.mem_sdiff, Set.mem_ofPred_eq and Set.sdiff_subset; zero_le takes implicit arguments.

Lean results (scratch project, frozen Submission olean):
- The three child types and the parent's frozen type elaborate in namespace GMT.Ch05.Submission.
- All four declarations are fully proved. #print axioms gives [propext, Classical.choice, Quot.sound] for each.
- A Submission-shaped copy with `example : <frozen type> := Submission.X` checks compiles. Its only sorry is the contract's main_theorem.
- The evidence is saved in the git-ignored GMT/Scratch/ble_sac/ with SHA256SUMS.

The proposed names are not reserved anywhere. An independent reviewer agent re-ran all checks and accepted.
