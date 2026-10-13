# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1.smooth_approximation-a1`
- Child DAG node: `root.harmonic_approximation-a1.smooth_approximation-a1.l2_approximate_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source and role. This is step 6 of the parent proof (w12_ball_smooth_approximation): mollification is an approximate identity in L^2 (cf. Gilbarg-Trudinger, Elliptic Partial Differential Equations of Second Order, Section 7.2 (mollifiers); Evans, Partial Differential Equations, Appendix C (properties of mollifiers)). It uses the sibling mollifier_l2_contraction (step 5 of the parent proof). The parent applies it twice, with E = R, H = 1_B f and with E = R^n, H = 1_B g.

Notation.
- n is a natural number, mu := Lebesgue measure (volume) on R^n, E is a real Banach space.
- Hypotheses: H : R^n -> E is integrable and H is in L^2(mu; E); for every j in N, rho_j : R^n -> R is continuous, rho_j >= 0, int rho_j = 1, rho_j(z) = 0 whenever ||z|| >= eps_j, and eps_j -> 0.
- For u : R^n -> E put (M_j u)(x) := int rho_j(z) u(x - z) dz (Bochner integral). This is Mathlib's convolution rho_j *[lsmul R R, volume] u (convolution_lsmul).
- For u : R^n -> E put N(u) := (int^- ||u(x)||_e^2 dx)^(1/2) in [0, infinity], so int^- ||u||_e^2 = N(u)^2 and N(-u) = N(u). For a.e. strongly measurable u, N(u) = eLpNorm u 2 mu (eLpNorm_eq_lintegral_rpow_enorm_toReal). This identification needs the measurability: in the pinned Mathlib, eLpNorm of a function that is not a.e. strongly measurable is defined to be infinity. Hence Minkowski's inequality N(u + v + w) <= N(u) + N(v) + N(w) holds for a.e. strongly measurable u, v, w (eLpNorm_add_le with 1 <= 2, which itself has no measurability hypothesis). Every function to which N is applied below is a.e. strongly measurable.

Proof.
1. The kernels. Fix j. If eps_j <= 0, then every z satisfies ||z|| >= 0 >= eps_j, so rho_j = 0 identically and int rho_j = 0, contradicting int rho_j = 1; hence eps_j > 0. If rho_j(z) is nonzero then ||z|| < eps_j, so support rho_j lies in ball(0, eps_j) and tsupport rho_j lies in closedBall(0, eps_j), which is compact because R^n is finite-dimensional. So rho_j is continuous with compact support; hence it is bounded, measurable and integrable.

2. Convolutions are defined, linear and continuous. Let u : R^n -> E be integrable and x in R^n. Since z -> x - z preserves mu, z -> u(x - z) is integrable; since rho_j is bounded and measurable, z -> rho_j(z) u(x - z) is integrable. Consequently, for integrable u, v and every x, (M_j(u - v))(x) = (M_j u)(x) - (M_j v)(x) (linearity of the Bochner integral). Moreover M_j u is continuous, because rho_j is continuous with compact support and u is locally integrable (HasCompactSupport.continuous_convolution_left); in particular M_j u is a.e. strongly measurable.

3. Contraction. Let u : R^n -> E be integrable; then u is a.e. strongly measurable and, by step 2, M_j u is continuous. The sibling theorem mollifier_l2_contraction, applied to the continuous kernel rho_j with rho_j >= 0 and int rho_j = 1 and to u, gives int^- ||(M_j u)(x)||_e^2 dx <= int^- ||u(x)||_e^2 dx, that is, N(M_j u) <= N(u).

4. Continuous compactly supported functions. Let Phi : R^n -> E be continuous with compact support and K := tsupport Phi (compact). Claim: N(M_j Phi - Phi) -> 0 as j -> infinity.
(a) Let K1 := {x : infEdist(x, K) <= 1}, the closed 1-thickening of K (Metric.cthickening 1 K; empty if K is empty). It is compact (IsCompact.cthickening, R^n being proper), so mu(K1) < infinity.
(b) Phi is uniformly continuous (HasCompactSupport.uniformContinuous_of_continuous). Let eta' > 0 and choose delta in (0, 1] such that dist(Phi(a), Phi(b)) <= eta' whenever dist(a, b) < delta. Since eps_j -> 0, there is J such that eps_j < delta for all j >= J.
(c) Let j >= J and x in R^n. We have support rho_j inside ball(0, eps_j), which lies inside ball(0, delta); rho_j >= 0; int rho_j = 1; and dist(Phi(y), Phi(x)) <= eta' for all y in ball(x, delta). Writing Phi(x) = int rho_j(z) Phi(x) dz, we get (M_j Phi)(x) - Phi(x) = int rho_j(z) (Phi(x - z) - Phi(x)) dz, and rho_j(z) nonzero forces ||z|| < delta, i.e. x - z in ball(x, delta). Hence ||(M_j Phi)(x) - Phi(x)|| <= int rho_j(z) eta' dz = eta'. (This is exactly Mathlib's dist_convolution_le.)
(d) Let j >= J and x not in K1. Then x is not in K (K is contained in K1), so Phi(x) = 0. Let z in R^n. If rho_j(z) is nonzero then ||z|| < eps_j < delta <= 1, so dist(x - z, x) < 1; if x - z were in K, then infEdist(x, K) <= edist(x, x - z) < 1 and x would lie in K1, a contradiction. Hence Phi(x - z) = 0. Thus the integrand rho_j(z) Phi(x - z) vanishes for every z, so (M_j Phi)(x) = 0 and (M_j Phi)(x) - Phi(x) = 0.
(e) By (c) and (d), for j >= J and every x, ||(M_j Phi)(x) - Phi(x)||_e^2 <= eta'^2 1_{K1}(x). Hence int^- ||M_j Phi - Phi||_e^2 <= eta'^2 mu(K1) for all j >= J. As mu(K1) < infinity and eta' > 0 is arbitrary, int^- ||M_j Phi - Phi||_e^2 -> 0, i.e. N(M_j Phi - Phi) -> 0.

5. Density. Let eta > 0. Since H is in L^2, 2 is finite, R^n is locally compact and Lebesgue measure is regular, there is Phi : R^n -> E continuous with compact support and N(H - Phi) <= eta (MemLp.exists_hasCompactSupport_eLpNorm_sub_le). Phi is integrable (continuous with compact support), so H - Phi is integrable; and N(Phi - H) = N(H - Phi) <= eta.

6. Splitting. For every j and every x, step 2 (applied to the integrable functions H - Phi and Phi) gives
(M_j H)(x) - H(x) = (M_j(H - Phi))(x) + ((M_j Phi)(x) - Phi(x)) + (Phi(x) - H(x)).
The three summands are a.e. strongly measurable (step 2 for the first two; H is a.e. strongly measurable and Phi is continuous). By Minkowski, step 3 with u = H - Phi, and step 5,
N(M_j H - H) <= N(M_j(H - Phi)) + N(M_j Phi - Phi) + N(Phi - H) <= eta + N(M_j Phi - Phi) + eta.

7. Conclusion. By step 4 there is J' such that N(M_j Phi - Phi) <= eta for all j >= J'. Then N(M_j H - H) <= 3 eta and int^- ||(M_j H)(x) - H(x)||_e^2 dx = N(M_j H - H)^2 <= 9 eta^2 for all j >= J'. Since eta > 0 was arbitrary, int^- ||int rho_j(z) H(x - z) dz - H(x)||_e^2 dx -> 0 in [0, infinity] (ENNReal.tendsto_nhds_zero). QED

Formalization note. MemLp.exists_hasCompactSupport_eLpNorm_sub_le lives in Mathlib.MeasureTheory.Function.ContinuousMapDense, which the frozen contract does not import; import it in GMT/Ch05/Submission.lean (the comparator byte-checks only the contract and build inputs). Every other cited lemma is available under the contract's imports (checked with lake env lean).

## Key steps

1. eps_j > 0 and rho_j is continuous with compact support; M_j u = rho_j * u is linear on L^1 and continuous
2. Contraction N(M_j u) <= N(u) from the sibling mollifier_l2_contraction
3. For Phi continuous with compact support: |M_j Phi - Phi| <= eta' uniformly and vanishes off the compact K1, so N(M_j Phi - Phi) -> 0
4. Density of C_c in L^2 and Minkowski: N(M_j H - H) <= 2 eta + N(M_j Phi - Phi)
5. eta arbitrary gives int^- ||M_j H - H||_e^2 -> 0

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
