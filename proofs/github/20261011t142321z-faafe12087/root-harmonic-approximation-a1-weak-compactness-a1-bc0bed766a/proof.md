# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1`
- Child DAG node: `root.harmonic_approximation-a1.weak_compactness-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source and role. This is fact (W) of the parent proof (Simon p. 114: grad f_{k'} converges weakly to grad w in L^2, with int |grad w|^2 <= 1). Bounded sequences in a Hilbert space have weakly convergent subsequences, and the norm is weakly lower semicontinuous (Evans, Appendix D.4; Brezis, Functional Analysis, Thm 3.18). No sibling is used.

Proof.
1. Hilbert space. Let mu := Lebesgue measure restricted to B and H := L^2(mu;R^n) = Lp (Rn n) 2 mu. H is a complete real Hilbert space with <u,v>_H = int_B <u(x), v(x)> dx (Mathlib MeasureTheory.L2.inner_def) and ||u||_H^2 = int_B |u|^2. Let gamma_k be the class of G_k in H (MemLp.toLp); then ||gamma_k||_H^2 = int_B |G_k|^2 <= 1. For h with MemLp h 2 mu and class h^, int_B <G_k, h> = <gamma_k, h^>_H, because representatives agree mu-a.e.

2. Separability. The Borel sigma-algebra of R^n is countably generated and mu is finite. So mu is separable and H is second countable (Mathlib instance MeasureTheory.Lp.SecondCountableTopology; R^n is separable). Let (e_j)_{j in N} enumerate a countable dense subset of H. If H = {0} (e.g. when n = 0), take e_j := 0, and everything below is trivial.

3. Diagonal extraction. For each j, |<gamma_k, e_j>| <= ||e_j|| for all k. By Bolzano-Weierstrass and a diagonal construction there is a strictly increasing phi such that l_j := lim_k <gamma_{phi(k)}, e_j> exists for every j. Concretely: choose nested strictly increasing maps sigma_0, sigma_1, ... with <gamma_{sigma_0 o ... o sigma_j (i)}, e_j> convergent in i, then set phi(k) := sigma_0 o ... o sigma_k (k); phi is strictly increasing and, from index j on, a subsequence of each sigma_0 o ... o sigma_j. (Equivalently, the points (<gamma_k, e_j>)_j lie in the compact metrizable product of the intervals [-||e_j||, ||e_j||]; apply IsCompact.tendsto_subseq.)

4. Convergence for all h in H. Let h be in H and eta > 0, and pick j with ||h - e_j|| <= eta. Then
|<gamma_{phi(k)}, h> - <gamma_{phi(l)}, h>| <= |<gamma_{phi(k)}, e_j> - <gamma_{phi(l)}, e_j>| + ||gamma_{phi(k)} - gamma_{phi(l)}|| ||h - e_j|| <= |<gamma_{phi(k)}, e_j> - <gamma_{phi(l)}, e_j>| + 2 eta,
which is <= 3 eta for k, l large. So L(h) := lim_k <gamma_{phi(k)}, h> exists for every h in H. L is linear, as a pointwise limit of linear functionals, and |L(h)| <= sup_k ||gamma_{phi(k)}|| ||h|| <= ||h||. Hence L is a continuous linear functional with ||L|| <= 1.

5. Riesz representation. Since H is complete, there is gamma in H with L(h) = <gamma, h>_H for all h in H and ||gamma|| = ||L|| <= 1 (Mathlib InnerProductSpace.toDual, a linear isometric equivalence between H and its dual).

6. Back to functions. Let g : R^n -> R^n be the function underlying gamma (the coercion of the Lp element). Then MemLp g 2 mu, and the lintegral over B of ||g||_e^2 equals ||gamma||^2 <= 1 (eLpNorm g 2 mu = ||gamma||). For h with MemLp h 2 mu and class h^: int_B <G_{phi(k)}, h> = <gamma_{phi(k)}, h^> -> L(h^) = <gamma, h^> = int_B <g, h>. This is the claim.
(Alternatively, steps 3-5 follow from the sequential Banach-Alaoglu theorem WeakDual.isSeqCompact_closedBall, applied to the functionals <gamma_k, .> in the closed unit ball of the dual of the separable space H, followed by InnerProductSpace.toDual.) QED

Formalization note. If needed, import Mathlib.MeasureTheory.Function.L2Space and Mathlib.MeasureTheory.Measure.SeparableMeasure in GMT/Ch05/Submission.lean.

## Key steps

1. Regard G_k as elements gamma_k of the Hilbert space H = L^2(B;R^n) with norm <= 1
2. H is separable; a diagonal subsequence makes <gamma_{phi(k)}, e_j> converge on a dense sequence (e_j)
3. Density and the uniform bound give a limit functional L(h) = lim <gamma_{phi(k)}, h> with norm <= 1
4. Riesz representation L = <gamma, .> with norm <= 1; g is the representative of gamma

## Reference use

### local-project

Queries:
- `for pat in 'Rellich' 'Kondrachov' 'Poincar' 'Weyl' 'weakly harmonic|weaklyHarmonic|WeaklyHarmonic' 'mean value property|meanValue|mean_value' 'Sobolev' 'weak derivative|weakDeriv|WeakDeriv|HasWeakDeriv' 'mollif|Mollif'; do rg -l -i "$pat" <snapshot>/mathlib/Mathlib; done`
- `rg -n 'theorem .*isSeqCompact|theorem .*exists_tendsto.*weak|seqCompact.*WeakDual|WeakDual.*SeqCompact' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem .*ae_eq_zero_of_integral_contDiff|theorem .*ae_eq_of_integral_contDiff' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem .*convolution_tendsto|theorem .*ae_convolution_tendsto|theorem .*tendsto_convolution' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem arzela_ascoli' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable|theorem integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable|theorem integral_bilinear_fderiv_right_eq_neg_left_of_integrable' <snapshot>/mathlib/Mathlib`
- `rg -n 'instance.*SecondCountableTopology.*Lp|SeparableSpace.*Lp|instance.*Lp.*SecondCountable|theorem .*secondCountableTopology' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `rg -n 'theorem MemLp.exists_hasCompactSupport|theorem .*exists_contDiff.*eLpNorm|theorem .*_dense' <snapshot>/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `rg -n '^(theorem|lemma|noncomputable def|def) ' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean`
- `rg -n 'theorem _root_\.HasCompactSupport\.(contDiff|hasFDerivAt|hasDerivAt|fderiv)' <snapshot>/mathlib/Mathlib/Analysis`
- `rg -n 'theorem (normed|nonneg_normed|integral_normed|support_normed_eq|hasCompactSupport_normed|contDiff_normed|tsupport_normed_eq)' <snapshot>/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `rg -n 'theorem tendsto_integral_smul_of_tendsto_average_norm_sub' -A 12 <snapshot>/mathlib/Mathlib`
- `rg -n -e 'def toDual' -e 'theorem contDiff_norm_sq' -e 'theorem tendstoInMeasure_of_tendsto_eLpNorm' -e 'theorem TendstoInMeasure.exists_seq_tendsto_ae' -e 'theorem cauchy_complete_eLpNorm' -e 'theorem IsCompact.tendsto_subseq' -e 'theorem integral_comp_inv_smul_of_nonneg' -e 'expNegInvGlue.contDiff' <snapshot>/mathlib/Mathlib/{Analysis,MeasureTheory,Topology}`
- `rg -n -e 'theorem convolution_symm' -e 'theorem convolution_flip' -e 'theorem integral_comp_smul ' -e 'theorem setIntegral_comp_smul' <snapshot>/mathlib/Mathlib/Analysis/Convolution.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `rg -l -i 'rellich|poincare_ineq|poincaré inequality|weyl|weakly harmonic|mollif|meanValue|mean_value|IsW12|weak gradient|weakGradient' .lake/packages/simongmt/Poincare`
- `rg -n '^(theorem|lemma|def|noncomputable def|structure)' .lake/packages/simongmt/Poincare/SimonGMT/Chapter05/*.lean`
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean`
- `grep -n -i 'harmonic approximation|Lemma 3.1|Rellich' book/sources/chapter-05-source.txt; sed -n 580,660p book/sources/chapter-05-source.txt`
- `lake env lean /tmp/hal-decomp-check/Check.lean (frozen-contract copy + the 7 child declarations + a HarmonicApproximationLemma assembly skeleton)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Module/WeakDual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Distribution/Sobolev.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/SeparableMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSpace/Complete.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Average.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Poincare.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-05-source.txt`
- `/tmp/hal-decomp-check/Check.lean`

Pinned snapshot: project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). The snapshot's GMT/Ch05/Contract.lean and Submission.lean are byte-identical to the workspace copies (cmp; Contract sha256 c966f51efddb5a68ce15ef2a2a322fd9df0ca69da4626c7acef05b05d1691e12), so the Lean check below applies to the frozen contract.

No usable matches:
- Mathlib has no Rellich/Kondrachov, weakly-harmonic, weak-derivative or mollifier API (0 files each).
- 'Poincar' hits only unrelated files (curve-integral Poincare lemma, Poincare conjecture, the hyperbolic metric).
- 'Weyl' hits only Lie-algebra and root-system files.
- 'Sobolev' hits only SobolevInequality.lean (Gagliardo-Nirenberg-Sobolev for compactly supported C^1 functions) and the Fourier-side Bessel-potential spaces (Analysis/Distribution/Sobolev.lean, BesselPotentialSpace.lean). Neither gives W^{1,2}(B) Poincare or Rellich.
- Mean-value hits are one-dimensional or complex only (Analysis/Complex/Harmonic/MeanValue.lean); there is no n-dimensional mean value property.
So Poincare, Rellich, weak compactness and Weyl must be proved; hence the children.

Usable Mathlib items cited in the child proofs, all verified to exist:
- Harmonic functions and Laplacian: HarmonicAt/HarmonicOnNhd and harmonicAt_congr_nhds (Harmonic/Basic.lean); laplacian_eq_iteratedFDeriv_orthonormalBasis (Laplacian.lean:171).
- Convolution: HasCompactSupport.contDiff_convolution_left and hasFDerivAt_convolution_left (ContDiff/Convolution.lean:427,91); convolution_assoc and convolution_symm (Convolution.lean:925,688).
- Bump functions: the ContDiffBump.normed API (BumpFunction/Normed.lean); ContDiffBump.convolution_tendsto_right_of_continuous and ae_convolution_tendsto_right_of_locallyIntegrable (BumpFunction/Convolution.lean:94,103).
- Distributions and integration by parts: IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (AEEqOfIntegralContDiff.lean:205); integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (LineDeriv/IntegrationByParts.lean:226).
- Compactness: BoundedContinuousFunction.arzela_ascoli (Bounded/ArzelaAscoli.lean:109); IsCompact.tendsto_subseq (Sequences.lean:298); WeakDual.isSeqCompact_closedBall (WeakDual.lean:369).
- Hilbert and Lp spaces: InnerProductSpace.toDual (Dual.lean:136); L2.inner_def (L2Space.lean:136); instance Lp.SecondCountableTopology (SeparableMeasure.lean:426); MemLp.exists_hasCompactSupport_eLpNorm_sub_le (ContinuousMapDense.lean:141); tendstoInMeasure_of_tendsto_eLpNorm and TendstoInMeasure.exists_seq_tendsto_ae (ConvergenceInMeasure.lean:452,273); cauchy_complete_eLpNorm (LpSpace/Complete.lean:370).
- Smooth functions and scaling: expNegInvGlue.contDiff (SmoothTransition.lean); contDiff_norm_sq (InnerProductSpace/Calculus.lean:140); integral_comp_inv_smul_of_nonneg and integral_comp_smul (Haar/NormedSpace.lean).
- Lebesgue differentiation with general kernels: tendsto_integral_smul_of_tendsto_average_norm_sub (Integral/Average.lean:835).
Several of these live in modules the contract does not import. The comparator byte-checks only the contract and build inputs, so they may be imported in GMT/Ch05/Submission.lean; the proofs note this.

simongmt (pinned package, outside the snapshot):
- No Rellich, no W^{1,2} Poincare, no Weyl lemma.
- Chapter04/Poincare.lean is Simon's varifold Poincare-type inequality, a different statement.
- Chapter08/DistributionalConstancy.lean (WeakDerivativesZero.fderiv_convolution_eq_zero, ae_constancyMollifier_convolution_tendsto) is a usable Lean template for the Weyl child's mollification steps.
- Chapter05 contains only graph-area and harmonic-energy algebra.

Book source (chapter-05-source.txt, about lines 588-645): the printed proof of Lemma 3.1 cites the Poincare inequality and Rellich's theorem ([GT01]) and weak L^2 convergence of the gradients with int|grad w|^2 <= 1, and concludes 'w is harmonic'. This matches the supplied proof and the children.

Lean check (/tmp/hal-decomp-check/Check.lean, lake env lean, exit 0): all seven child types elaborate in namespace GMT.Ch05.Submission after the frozen contract. An assembly skeleton of HarmonicApproximationLemma from the Poincare, Rellich, weak-compactness and Weyl children type-checks; the glue is left as sorry, and the only warnings are sorry and a push_neg deprecation.

Public sources consulted: Wikipedia 'Weyl's lemma (Laplace equation)'; University of Hamburg PDE lecture notes (radial-kernel mean value argument); TauCeti PR #14110, which cites Hormander ALPDO I Thm 4.4.1 and Folland Cor. 2.20. Textbook citations in the proofs either follow the parent proof (GT (7.45), Thm 7.26) or are section-level (Evans sections 5.3, 5.7, 5.8, App. D).
