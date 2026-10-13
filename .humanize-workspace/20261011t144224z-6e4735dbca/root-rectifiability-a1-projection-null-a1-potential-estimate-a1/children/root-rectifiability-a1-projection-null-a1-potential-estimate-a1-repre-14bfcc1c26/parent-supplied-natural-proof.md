# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1.projection_null-a1.potential_estimate-a1`
- Child DAG node: `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.representation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 4 of the parent proof. This is the representation formula in Gilbarg–Trudinger's proof of Lemma 7.14, u(x) = (nω_n)⁻¹∫ Σ_i (x_i − y_i)D_iu(y)|x − y|^{−n} dy for u ∈ C¹₀, written in the variable t = y − (integration variable). Let c := (m + 1)·ω, so K_j(t) = t_j/(c·|t|^{m+1}).

1. Constants. ω > 0 because B_1(0) is nonempty and open (measure_ball_pos), and ω < ∞. So c > 0. Also a is C¹.

2. Integrability of each term. By kernel_local_integrable (with this j and c), K_j is locally integrable. By convolution_smooth (with K = K_j, the given a, and v = e_j), t ↦ K_j(t)·∂_j a(y − t) is integrable for each j.

3. Sum inside. By Step 2 and linearity of the integral over a finite sum (integral_finsetSum, formerly integral_finset_sum), Σ_j ∫ K_j(t)·∂_j a(y − t) dt = ∫ Σ_j K_j(t)·∂_j a(y − t) dt.

4. Pointwise identity. For every linear functional Λ : ℝⁿ → ℝ and every v ∈ ℝⁿ we have v = Σ_j v_j·e_j. This is OrthonormalBasis.sum_repr for EuclideanSpace.basisFun, whose vectors are the e_j and whose coordinates are the v_j. Hence Λv = Σ_j v_j·Λe_j. Apply this with Λ = Da(y − t) and v = t. For every t ∈ ℝⁿ (including t = 0, where both sides are 0) this gives
 Σ_j K_j(t)·∂_j a(y − t) = Σ_j t_j·Da(y − t)e_j/(c·|t|^{m+1}) = Da(y − t)t/(c·|t|^{m+1}) =: G(t).

5. So G is integrable, as a finite sum of the integrable functions of Step 2 (integrable_finsetSum). The left side of the claim equals ∫ G(t) dt.

6. Polar coordinates. Apply polar_integral to G: ∫ G = ∫_S (∫_{(0,∞)} r^m·G(rθ) dr) dσ(θ), where S is the unit sphere and σ = (Lⁿ).toSphere.

7. Inner integrals. Fix θ ∈ S. Then |θ| = 1, so θ ≠ 0. For r > 0 we have |rθ| = r and Da(y − rθ)(rθ) = r·Da(y − rθ)θ. Hence
 r^m·G(rθ) = r^m·r·Da(y − rθ)θ/(c·r^{m+1}) = Da(y − rθ)θ/c.
Now use setIntegral_congr_fun on (0,∞), pull out 1/c (integral_div), and apply ray_ftc (a is C¹ with compact support, θ ≠ 0):
 ∫_{(0,∞)} r^m·G(rθ) dr = (1/c)·∫_{(0,∞)} Da(y − rθ)θ dr = a(y)/c.

8. Outer integral. The inner integral is the constant a(y)/c, so ∫_S a(y)/c dσ = σ(S)·a(y)/c (integral_const). By Measure.toSphere_real_apply_univ and finrank_euclideanSpace_fin, σ(S) = (finrank ℝ ℝⁿ)·Lⁿ(B_1(0)) = (m + 1)·ω = c. Since c > 0, the result is c·a(y)/c = a(y).

9. Steps 3–8 together give Σ_j ∫ K_j(t)·∂_j a(y − t) dt = ∫ G = a(y). ∎

## Key steps

1. Each t ↦ K_j(t)∂_j a(y−t) is integrable (kernel_local_integrable + convolution_smooth), so the sum moves inside the integral.
2. Expanding t in the standard basis gives Σ_j K_j(t)∂_j a(y−t) = G(t) := Da(y−t)t/((m+1)ω|t|^{m+1}).
3. polar_integral gives ∫G = ∫_S ∫_0^∞ r^m G(rθ) dr dσ, and r^m G(rθ) = Da(y−rθ)θ/((m+1)ω) for r > 0, |θ| = 1.
4. By ray_ftc each inner integral is a(y)/((m+1)ω), and σ(S) = (m+1)ω gives a(y).

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
