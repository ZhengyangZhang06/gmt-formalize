# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1.projection_null-a1.potential_estimate-a1`
- Child DAG node: `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.polar_integral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: formula (P) in Step 1 of the parent proof. The argument is Mathlib's proof of integral_fun_norm_addHaar (HaarToSphere.lean), with the radial integrand replaced by a general integrable g. Notation: E := Eucl n. finrank ℝ E = m + 1 (finrank_euclideanSpace_fin), so finrank ℝ E − 1 = m. Let ν := Measure.volumeIoiPow m. This is the measure on the subtype (0,∞) = Ioi 0 obtained from Lebesgue measure by comap along the inclusion, with density r ↦ ENNReal.ofReal(r^m).

1. The polar homeomorphism. Let Φ := homeomorphUnitSphereProd E : E∖{0} → S × (0,∞), Φ(x) = (|x|⁻¹x, |x|), with inverse (θ, r) ↦ rθ. By Measure.measurePreserving_homeomorphUnitSphereProd, after rewriting finrank ℝ E − 1 = m, Φ is measure preserving from λ₀ := (Lⁿ).comap Subtype.val (Lebesgue measure transported to the subtype E∖{0}) to σ ⊗ ν. As a homeomorphism, Φ is a measurable embedding.

2. The transported integrand. Define G : S × (0,∞) → ℝ by G(θ, r) := g(rθ). For x ∈ E∖{0}, G(Φ(x)) = g(|x|·(|x|⁻¹x)) = g(x), because |x| ≠ 0 (smul_smul, mul_inv_cancel₀, one_smul).

3. Removing the origin. The set {0}ᶜ is measurable and {0} is Lⁿ-null. So ∫_E g dLⁿ = ∫_{{0}ᶜ} g dLⁿ = ∫_{x ∈ E∖{0}} g(x) dλ₀(x), by integral_subtype_comap for the measurable set {0}ᶜ and restrict_compl_singleton.

4. Change of variables. MeasurePreserving.integral_comp, applied to the measurable embedding Φ, gives ∫ G(Φ(x)) dλ₀(x) = ∫ G d(σ ⊗ ν). By Step 2 the left side is ∫ g(x) dλ₀(x). With Step 3, ∫_E g = ∫ G d(σ ⊗ ν).

5. Integrability on the product. g is integrable on {0}ᶜ, so g ∘ Subtype.val is λ₀-integrable (integrableOn_iff_comap_subtypeVal). Since G ∘ Φ = g ∘ Subtype.val by Step 2, MeasurePreserving.integrable_comp_emb shows that G is (σ ⊗ ν)-integrable.

6. Fubini. σ is a finite measure and ν is σ-finite (Mathlib instances). So integral_prod gives ∫ G d(σ ⊗ ν) = ∫_S (∫_{(0,∞)} g(rθ) dν(r)) dσ(θ).

7. Unfolding ν. Fix θ ∈ S. ENNReal.ofReal(r^m) is the coercion of the measurable ℝ≥0-valued function r ↦ Real.toNNReal(r^m). Hence integral_withDensity_eq_integral_smul gives ∫ g(rθ) dν(r) = ∫_{r ∈ Ioi 0} Real.toNNReal(r^m) • g(rθ) d((volume).comap Subtype.val). Then integral_subtype_comap with measurableSet_Ioi turns this into the set integral ∫_{(0,∞)} Real.toNNReal(r^m) • g(rθ) dr. For r > 0 we have r^m ≥ 0, so Real.toNNReal(r^m) • g(rθ) = r^m·g(rθ) (NNReal.smul_def, Real.coe_toNNReal). By setIntegral_congr_fun on the measurable set (0,∞), the inner integral equals ∫_{(0,∞)} r^m·g(rθ) dr, for every θ ∈ S.

8. Steps 3–7 together give ∫_E g(x) dx = ∫_S (∫_{(0,∞)} r^m·g(rθ) dr) dσ(θ). ∎

## Key steps

1. Φ = homeomorphUnitSphereProd carries Lebesgue measure on ℝⁿ∖{0} to σ ⊗ volumeIoiPow m (measurePreserving_homeomorphUnitSphereProd, with finrank − 1 = m), and G∘Φ = g for G(θ, r) = g(rθ).
2. ∫ g = ∫_{ℝⁿ∖{0}} g = ∫ G d(σ⊗ν): remove the null point, then change variables; G is integrable by integrable_comp_emb.
3. Apply Fubini (integral_prod). For every θ, unfold ν = r^m dr on (0,∞) (integral_withDensity_eq_integral_smul, integral_subtype_comap).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c95; mathlib_commit 25730c7c)`
- `sha256sum GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean; diff (both ea3ee0dd…, identical)`
- `python3 gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') (replayed header: open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06; three opens; noncomputable section; end)`
- `grep -n 'theorem\|lemma\|def \|abbrev ' Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`
- `grep -rn 'homeomorphUnitSphereProd\|toSphere' Mathlib --include=*.lean (matches only HaarToSphere.lean and Analysis/Normed/Module/Ball/RadialEquiv.lean)`
- `grep -n 'contDiff_convolution_right\|hasFDerivAt_convolution_right\|convolutionExists_right\|convolution_precompR_apply\|convolution_lsmul\|def ConvolutionExistsAt' Mathlib/Analysis/Convolution.lean Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `grep -n 'theorem integral_Ioi_of_hasDerivAt_of_tendsto\|integral_Ioi_deriv_eq' Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `grep -rn 'setIntegral_mono_set\|setIntegral_mono_on\|setIntegral_const\|integral_inter_add_sdiff\|integrableOn_of_bounded\|norm_integral_le_of_norm_le\|measurePreserving_div_left\|setIntegral_congr_fun\|integral_indicator' Mathlib/MeasureTheory`
- `grep -n 'norm_apply_le' Mathlib/Analysis/Normed/Lp/PiLp.lean; grep -n 'sum_repr\|basisFun_apply\|basisFun_repr' Mathlib/Analysis/InnerProductSpace/PiL2.lean; grep -n 'HasCompactSupport.fderiv\|continuous_fderiv' Mathlib/Analysis/Calculus/FDeriv/Const.lean Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `python3 verifier/lean_contract.py validate_lean_statement on the 8 lean_statements`
- `lean AllChildren.lean, Assembly.lean, Short.lean, Short2.lean, C1.lean, C3.lean, C7.lean, C8.lean, EndToEnd.lean, Solutions.lean (LEAN_PATH = workspace .lake/build/lib/lean + lake-packages-25730c7c/*/.lake/build/lib/lean)`
- `python3 lean_name scan of dag.json and nodes/*/decomposition-v*.json (477 reserved names; none starts with rpn_pe)`
- `ls /tmp/rpn_v3_nmhI8O1x /tmp/rpn_v2_Yfpb0s4j; find /tmp -maxdepth 4 -name '*.lean' | grep C1Rev (the handoff's witness files: no match)`

Files inspected:
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-potential-estimate-a1/parent-child-handoff.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-potential-estimate-a1/parent-supplied-plan.md`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-potential-estimate-a1/parent-supplied-natural-proof.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1/decomposition-v3.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1/decomposition-scope-v3.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1/decomposition-audit-v3.json`
- `GMT/Ch06/Contract.lean`
- `GMT/Ch06/Submission.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Ball/RadialEquiv.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Convolution.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Group/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/pe-decomp-ch06/AllChildren.lean`
- `/tmp/pe-decomp-ch06/Assembly.lean`
- `/tmp/pe-decomp-ch06/Short.lean`
- `/tmp/pe-decomp-ch06/Short2.lean`
- `/tmp/pe-decomp-ch06/C1.lean`
- `/tmp/pe-decomp-ch06/C3.lean`
- `/tmp/pe-decomp-ch06/C7.lean`
- `/tmp/pe-decomp-ch06/C8.lean`
- `/tmp/pe-decomp-ch06/EndToEnd.lean`
- `/tmp/pe-decomp-ch06/Solutions.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract. It is byte-identical to the workspace Contract.lean and Submission.lean (sha256 ea3ee0dd…), which define Eucl P := EuclideanSpace ℝ (Fin P) in namespace GMT.Ch06. Before each child type the comparator replays: open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06; three opens; noncomputable section; end.
The pinned Mathlib supplies every tool the children use:
 – polar coordinates: Measure.toSphere, toSphere_real_apply_univ, volumeIoiPow, measurePreserving_homeomorphUnitSphereProd, integrableOn_fun_norm_addHaar, integral_fun_norm_addHaar (HaarToSphere.lean:51,92,113,142,273,296) and homeomorphUnitSphereProd (RadialEquiv.lean:67);
 – convolution calculus: convolution_lsmul, HasCompactSupport.convolutionExists_right, convolution_precompR_apply (Convolution.lean:423,316,970); HasCompactSupport.hasFDerivAt_convolution_right and contDiff_convolution_right (ContDiff/Convolution.lean:61,420); HasCompactSupport.fderiv and fderiv_apply (FDeriv/Const.lean:389); ContDiff.continuous_fderiv (ContDiff/Defs.lean:1271);
 – ray FTC: integral_Ioi_of_hasDerivAt_of_tendsto and HasCompactSupport.integral_Ioi_deriv_eq (IntegralEqImproper.lean:786,820);
 – set integrals: integral_inter_add_sdiff, setIntegral_mono_set, setIntegral_mono_on, setIntegral_const, integral_indicator, setIntegral_congr_fun (Bochner/Set.lean); Measure.integrableOn_of_bounded (IntegrableOn.lean:716); norm_integral_le_of_norm_le and integral_const (Bochner/Basic.lean:985,992);
 – measure invariance: measurePreserving_div_left, whose additive form is measurePreserving_sub_left (Group/Measure.lean:393);
 – coordinates and bases: PiLp.norm_apply_le (PiLp.lean:713); OrthonormalBasis.sum_repr, EuclideanSpace.basisFun_apply and basisFun_repr (PiL2.lean:494,806,810).
No match: Mathlib has no polar-coordinate formula for non-radial integrands. homeomorphUnitSphereProd and toSphere are used only in HaarToSphere.lean, so polar_integral is a genuine obligation. The handoff's witness files (/tmp/rpn_v3_nmhI8O1x, /tmp/rpn_v2_Yfpb0s4j) are not present on this machine.
Lean evidence. It is a formalization aid, not part of any natural proof, and is in /tmp/pe-decomp-ch06 on this machine.
 – AllChildren.lean: the 8 child types elaborate.
 – Assembly.lean: the frozen parent type follows from the 8 child types.
 – Short2.lean, C3.lean, Short.lean, C1.lean, C7.lean, C8.lean: sorry-free proofs of each child; each file stubs only its declared siblings.
 – EndToEnd.lean: all 8 proofs plus the parent with no sorry; its only axioms are propext, Classical.choice and Quot.sound.
 – Solutions.lean: the comparator-style exact checks pass for 9 targets.
The scratch proofs use the deprecated aliases Set.diff_subset and Set.inter_union_diff (warnings only).
All 8 lean_names are free among the 477 reserved names.
