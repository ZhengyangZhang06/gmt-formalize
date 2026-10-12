# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1.smooth_approximation-a1`
- Child DAG node: `root.harmonic_approximation-a1.smooth_approximation-a1.l2_contraction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source and role. This is step 5 of the parent proof (w12_ball_smooth_approximation): the L^2 contraction property of convolution with a probability kernel, i.e. Young's convolution inequality with exponents (1, 2; 2) for a nonnegative kernel of mass one (cf. Gilbarg-Trudinger, Elliptic Partial Differential Equations of Second Order, Section 7.2 (mollifiers); Evans, Partial Differential Equations, Appendix C (mollifiers)). The sibling mollifier_l2_tendsto uses it.

Notation.
- n is a natural number, mu := Lebesgue measure (volume) on R^n, E is a real Banach space.
- All lintegrals (written int^-) take values in [0, infinity]; ||.||_e is the extended norm.
- rho : R^n -> R is continuous, rho(z) >= 0 for all z, and int rho dmu = 1 (Bochner integral).
- H : R^n -> E is mu-a.e. strongly measurable.
- a(z) := ofReal(rho(z)) in [0, infinity), h(y) := ||H(y)||_e in [0, infinity), and I := int^- h(y)^2 dy, the right-hand side of the claim.

Proof.
1. Mass one. Since int rho = 1 is nonzero and the Bochner integral of a non-integrable function is 0, rho is integrable (Mathlib: integrable_of_integral_eq_one). Since rho >= 0, int^- a dmu = ofReal(int rho dmu) = 1 (ofReal_integral_eq_lintegral_ofReal).

2. Measurability. a is measurable because rho is continuous. Since H is a.e. strongly measurable, h is a.e. measurable. Lebesgue measure is invariant under translations and under z -> -z, so for each fixed x the map z -> x - z preserves mu (Measure.measurePreserving_sub_left); hence z -> h(x - z) is a.e. measurable. The map (x, z) -> x - z is quasi-measure-preserving from mu (x) mu to mu (quasiMeasurePreserving_sub), so (x, z) -> a(z) h(x - z)^2 is a.e. measurable for the product measure mu (x) mu.

3. Pointwise bound. Fix x in R^n. For every function, the extended norm of its Bochner integral is at most the lintegral of its extended norm (enorm_integral_le_lintegral_enorm; if the integrand is not integrable the Bochner integral is 0 and the bound is trivial). Since rho(z) >= 0 we have ||rho(z) . v||_e = |rho(z)| ||v||_e = a(z) ||v||_e for v in E. Therefore
||int rho(z) H(x - z) dz||_e <= int^- a(z) h(x - z) dz.

4. Weighted Cauchy-Schwarz. Fix x. Put u(z) := a(z)^(1/2) and v(z) := a(z)^(1/2) h(x - z). Both are a.e. measurable [0, infinity]-valued functions (step 2), u(z) v(z) = a(z) h(x - z), u^2 = a and v(z)^2 = a(z) h(x - z)^2. Hoelder's inequality for lintegrals with exponents p = q = 2 (ENNReal.lintegral_mul_le_Lp_mul_Lq with Real.HolderConjugate.two_two; no finiteness assumption is needed) gives
int^- a(z) h(x - z) dz <= (int^- a)^(1/2) (int^- a(z) h(x - z)^2 dz)^(1/2) = (int^- a(z) h(x - z)^2 dz)^(1/2),
using int^- a = 1 from step 1. Squaring (t -> t^2 is monotone on [0, infinity]) gives
(int^- a(z) h(x - z) dz)^2 <= int^- a(z) h(x - z)^2 dz.

5. Combining steps 3 and 4 (squaring is monotone on [0, infinity]): for every x in R^n,
||int rho(z) H(x - z) dz||_e^2 <= int^- a(z) h(x - z)^2 dz.

6. Integrating step 5 over x (the lintegral is monotone and needs no measurability of the smaller function):
int^-_x ||int rho(z) H(x - z) dz||_e^2 dx <= int^-_x int^-_z a(z) h(x - z)^2 dz dx.

7. Tonelli and translation invariance. By step 2 and sigma-finiteness of mu, the order of integration may be exchanged (lintegral_lintegral_swap):
int^-_x int^-_z a(z) h(x - z)^2 dz dx = int^-_z int^-_x a(z) h(x - z)^2 dx dz = int^-_z a(z) (int^-_x h(x - z)^2 dx) dz,
where the finite constant a(z) was pulled out of the inner lintegral (lintegral_const_mul'). By translation invariance of mu (lintegral_sub_right_eq_self), int^-_x h(x - z)^2 dx = int^-_y h(y)^2 dy = I for every z. Hence the double integral equals int^-_z a(z) I dz = (int^- a) I = I, using lintegral_mul_const (a is measurable by step 2) and step 1.

8. Conclusion. Steps 6 and 7 give
int^-_x ||int rho(z) H(x - z) dz||_e^2 dx <= I = int^-_x ||H(x)||_e^2 dx,
which is the claim. QED

Formalization note. All lemmas cited above are available under the imports of the frozen contract (checked with lake env lean against Mathlib 25730c7c). The Lean statement uses the explicit integral form int rho(z) . H(x - z) dz, which is definitionally Mathlib's convolution rho *[lsmul R R, volume] H (convolution_lsmul is rfl).

## Key steps

1. rho is integrable and the weight a = ofReal(rho) has lintegral 1
2. Pointwise: ||int rho(z) H(x - z) dz||_e <= int^- a(z) ||H(x - z)||_e dz
3. Weighted Cauchy-Schwarz (Hoelder p = q = 2) with mass-one weight: square <= int^- a(z) ||H(x - z)||_e^2 dz
4. Tonelli plus translation invariance: int^-_x int^-_z a(z) ||H(x - z)||_e^2 = int^- ||H||_e^2

## Reference use

### local-project

Queries:
- `rg -n "theorem _root_\.HasCompactSupport\.(contDiff_convolution_left|hasFDerivAt_convolution_left|hasFDerivAt_convolution_right|contDiff_convolution_right)" -A 8 <snapshot>/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `rg -n "theorem convolution_lsmul|theorem convolution_def|theorem convolution_flip|theorem convolution_eq_swap|theorem integral_sub_left_eq_self|theorem integral_sub_right_eq_self|theorem convolution_tendsto_right|theorem dist_convolution_le|theorem convolution_precompR_apply|theorem convolution_sub|theorem ConvolutionExistsAt|theorem _root_.HasCompactSupport.convolutionExists" <snapshot>/mathlib/Mathlib/Analysis/Convolution.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `rg -n -i young <snapshot>/mathlib/Mathlib -l; rg -n "eLpNorm_convolution|convolution.*eLpNorm|memLp_convolution|MemLp.convolution|Lp.*convolution|convolution_memLp" <snapshot>/mathlib/Mathlib`
- `rg -n "^theorem|^lemma|^protected theorem|^variable|^instance|^noncomputable def|^def|^protected def" <snapshot>/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean; rg -n instance <snapshot>/mathlib/Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`
- `rg -n "theorem setLIntegral_le_lintegral|theorem setLIntegral_congr_fun|theorem memLp_indicator_iff_restrict|theorem integrable_indicator_iff|theorem MemLp.mono_exponent|theorem MemLp.locallyIntegrable|theorem tendsto_of_tendsto_of_tendsto_of_le_of_le " <snapshot>/mathlib/Mathlib`
- `rg -n "theorem MemLp.exists_hasCompactSupport_eLpNorm_sub_le" -B 2 -A 6 <snapshot>/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `rg -n "continuous_convolution_left|continuous_convolution_right" <snapshot>/mathlib/Mathlib/Analysis/Convolution.lean; rg -n "(lemma|theorem) (lintegral|integral)_(sub|div)_(right|left)_eq_self" <snapshot>/mathlib/Mathlib; rg -n "(lemma|theorem) (quasiMeasurePreserving|measurePreserving)_(sub|div)" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem lintegral_mul_le_Lp_mul_Lq|theorem lintegral_lintegral_swap|theorem enorm_integral_le_lintegral_enorm|theorem ofReal_integral_eq_lintegral_ofReal|theorem eLpNorm_add_le |uniformContinuous_of_continuous" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem eLpNorm_of_not_aestronglyMeasurable" -A 4 <snapshot>/mathlib/Mathlib; sed -n 87,99p <snapshot>/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean`
- `rg -n "integral_inner\b|theorem integral_apply|theorem lintegral_mul_const" <snapshot>/mathlib/Mathlib`
- `rg -l -i "convolution|mollif|ContDiffBump" .lake/packages/simongmt/Poincare; rg -n "^(theorem|lemma) .*(convolution|mollif|Mollif)" .lake/packages/simongmt/Poincare; rg -n -i "young|approximate identity|eLpNorm.*convolution" .lake/packages/simongmt/Poincare`
- `for nm in mollifier_l2_contraction mollifier_l2_tendsto w12_ball_mollification_gradient; do rg -l $nm <run-dir> .lake/packages/simongmt/Poincare; done`
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean`
- `lake env lean /tmp/sa-decomp-check/Check1.lean (byte copy of the frozen contract + the 3 child types as sorry stubs, contract imports only)`
- `lake env lean /tmp/sa-decomp-check/Check2.lean (contract + BumpFunction.Normed/InnerProduct imports + children as sorry stubs + complete Lean proof of w12_ball_smooth_approximation + #print axioms)`
- `lake env lean /tmp/sa-decomp-check/Probe.lean, ProbeAvail2.lean, ProbeAvail4.lean, ProbeAvail6.lean (instantiation of the cited lemmas on Rn n with volume; availability under the contract imports alone)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Group/LIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Group/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Group/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/TriangleInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Indicator.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-smooth-approximation-a1/parent-child-handoff.json`
- `/tmp/sa-decomp-check/Check1.lean`
- `/tmp/sa-decomp-check/Check2.lean`
- `/tmp/sa-decomp-check/Probe.lean`
- `/tmp/sa-decomp-check/ProbeAvail6.lean`

Paths: <snapshot> = .humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7 (manifest: project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d). The snapshot's Contract.lean is byte-identical to the workspace contract (cmp), and Submission.lean is currently byte-identical to the contract.

No-match results (these justify the children):
- Mathlib has no Young convolution inequality and no L^p approximate-identity theorem. 'young' hits only Young diagrams/tableaux and the product inequality in MeanInequalities.lean. The only L^p convolution results are pointwise bounds: eLpNorm_convolution_integrand_le, ConvolutionExists.of_memLp_memLp and enorm_convolution_le (Analysis/Convolution.lean:536-561). Hence the l2_contraction and l2_approximate_identity children.
- simongmt has no L^2 mollifier convergence either. Its 'Young' hits in Chapter05 are the elementary Cauchy-Young product inequality.

Usable items, all verified to exist and to instantiate on Rn n with volume (Probe.lean):
- Convolution calculus: HasCompactSupport.contDiff_convolution_left and hasFDerivAt_convolution_left (ContDiff/Convolution.lean:427, 91); HasCompactSupport.continuous_convolution_left (Convolution.lean:724); convolution_lsmul (Convolution.lean:423, rfl); dist_convolution_le (Convolution.lean:814).
- Density: MemLp.exists_hasCompactSupport_eLpNorm_sub_le (ContinuousMapDense.lean:141).
- Lintegral and measure tools: ENNReal.lintegral_mul_le_Lp_mul_Lq (MeanInequalities.lean:202); lintegral_lintegral_swap (Measure/Prod.lean:1071); lintegral_sub_right_eq_self, Measure.measurePreserving_sub_left and quasiMeasurePreserving_sub (additive versions of Group/LIntegral.lean:69, Group/Measure.lean:393, Group/Prod.lean:458); enorm_integral_le_lintegral_enorm (Bochner/Basic.lean:333).
- L^p norms: eLpNorm_add_le (TriangleInequality.lean:54) has no measurability hypothesis. However, eLpNorm is defined to be infinity for functions that are not a.e. strongly measurable (LpSeminorm/Defs.lean:87-99), so the mollifier_l2_tendsto proof tracks measurability.
- Bump kernels: ContDiffBump.normed with contDiff_normed, continuous_normed, nonneg_normed, integral_normed and support_normed_eq (BumpFunction/Normed.lean:37-72), plus the HasContDiffBump instance for inner product spaces (BumpFunction/InnerProduct.lean:57).
- Zero extension and squeezing: memLp_indicator_iff_restrict (LpSeminorm/Indicator.lean:154); MemLp.mono_exponent (CompareExp.lean:137); integrable_indicator_iff (IntegrableOn.lean:340); setLIntegral_congr_fun and setLIntegral_le_lintegral (Lebesgue/Basic.lean:298, 258).
- Map-valued and inner-product integrals: ContinuousLinearMap.integral_apply (Bochner/ContinuousLinearMap.lean:73); integral_inner (Function/L2Space.lean:89).

Import availability: everything above is available under the contract's imports except three items (lake env lean probes ProbeAvail2/4/6): MemLp.exists_hasCompactSupport_eLpNorm_sub_le (ContinuousMapDense), ContDiffBump.normed (BumpFunction.Normed/InnerProduct) and integral_inner (L2Space). The child notes say so, and the comparator byte-checks only the contract and build inputs.

Reuse template: simongmt Chapter08/DistributionalConstancy.lean, WeakDerivativesZero.fderiv_convolution_eq_zero, is a kernel-checked template for the mollified_gradient child. It uses the reflected kernel as a test function and differentiates the convolution.

Name check: the three proposed names have no hits in the run directory (dag.json, nodes) or in simongmt.

Lean checks:
- Check1.lean: the three child types elaborate in GMT.Ch05.Submission with the contract imports alone.
- Check2.lean: the exact frozen parent type (byte-compared with the handoff) is proved from the three children with no sorry of its own; #print axioms shows sorryAx only through the stubs.

Web: a quick search could not confirm exact Gilbarg-Trudinger and Evans lemma numbers, so the child proofs cite them at section level (GT 7.2-7.3; Evans 5.3.1 and Appendix C).
