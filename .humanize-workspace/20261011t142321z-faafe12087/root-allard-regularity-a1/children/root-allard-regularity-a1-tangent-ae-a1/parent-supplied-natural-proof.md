# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1`
- Child DAG node: `root.allard_regularity-a1.tangent_ae-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 3, Def. 1.4, 1.7, Lemma 1.2, Rem. 1.3, Thm. 1.6 ('=>'), Rem. 1.8(1),(2), Thm. 1.9 (the fact (F1) of the parent proof), with the measurability step made explicit.

Notation. M := V.carrier (a subset of U), theta := V.mult, mu := V.weight = theta H^n restricted to M (theta := 0 off M), p_x := V.tangentProj x, eta_{x,r}(w) := (w - x)/r, B_r(x) the closed ball, B^o_r(x) the open ball, omega_n := unitBallVolume n; for an n-dimensional subspace P, p_P := P.starProjection. Hypotheses: U open; M is H^n-null-measurable and countably n-rectifiable; theta > 0 on M, theta is H^n-a.e.-measurable on M, and theta is H^n-integrable on M cap K for every compact K contained in U.

1. Two reductions.
 (a) mu(R^(n+l) minus M) = 0, and a set N contained in M is mu-null iff it is H^n-null: if H^n(N) = 0 then mu(N) = 0; conversely, if mu(N) = 0 take an H^n-measurable N' containing N with mu(N' cap M) = 0 (measurable hull); then integral_{N' cap M} theta dH^n = 0 with theta > 0 on M forces H^n(N' cap M) = 0. Hence (ii) and (iii) follow once they are proved at H^n-a.e. x in M, and (i) follows once p is shown to be a mu-a.e. limit of Borel maps.
 (b) [Simon Ch. 3, Def. 1.7 = SimonGMT Chapter03.HasWeightedApproximateTangentSpaceAt, the predicate used to define tangentProj] An n-dimensional subspace P is an approximate tangent space of M w.r.t. theta at x if lim_{r -> 0+} integral_{eta_{x,r}(M)} f(z) theta(x + r z) dH^n(z) = theta(x) integral_P f dH^n for every f in C_c(R^(n+l)). Since H^n(x + r E) = r^n H^n(E), for x in U and r so small that x + r spt f is a compact subset of U,
 (*) integral_{eta_{x,r}(M)} f(z) theta(x + r z) dH^n(z) = r^-n integral_M f((w - x)/r) theta(w) dH^n(w) = r^-n integral f((w - x)/r) dmu(w),
 and this integral is finite because theta is H^n-integrable on M cap K for compact K in U. If x in M then theta(x) > 0, so such a P is unique (SimonGMT HasWeightedApproximateTangentSpaceAt.unique), and by the definition of tangentProj, p_x = p_P whenever such a P exists; then dim P = n.

2. Localization. Let U_k := {x : |x| < k and B_{1/k}(x) is contained in U} (closed balls; this avoids distances to a possibly empty complement). U_k is open (if B_{1/k}(x) is contained in U then, by compactness, so is B_{1/k + eps}(x) for some eps > 0), its closure is a compact subset of U (if x_m -> x with B_{1/k}(x_m) in U then B^o_{1/k}(x) is contained in U, so x in U, and the closure is bounded), and U = union_k U_k (U is open). Put M_k := M cap U_k: it is H^n-measurable, countably n-rectifiable (a subset of M) and integral_{M_k cap K} theta dH^n < infinity for every compact K in R^(n+l). If x in M_k, spt f is contained in B_rho'(0) and r rho' is so small that B_{r rho'}(x) is contained in U_k (possible since U_k is open), then f((w - x)/r) != 0 implies w in U_k, so the integrals (*) for (M, theta) and for (M_k, theta) coincide; hence the approximate tangent spaces of (M, theta) and (M_k, theta) at x coincide (existence and value), and mu(B_r(x)) = (theta H^n restricted to M_k)(B_r(x)) for small r. As M = union_k M_k, it suffices to prove (ii) and (iii) at H^n-a.e. point of each M_k for the pair (M_k, theta), which satisfies the global hypotheses of Simon Ch. 3, 1.7-1.9. In steps 3 and 4 we therefore assume integral_{M cap K} theta dH^n < infinity for every compact K, so that mu is a Radon measure on R^(n+l).

3. Existence of T_x(M, theta) for H^n-a.e. x in M (Simon Ch. 3, Thm. 1.9).
 (a) [Ch. 3, Lemma 1.2 and Rem. 1.3] Since M is countably n-rectifiable there are an H^n-null set N_0 and embedded n-dimensional C^1 submanifolds N_1, N_2, ... of R^(n+l) with M contained in union_{j >= 0} N_j. (Proof of Lemma 1.2: M is contained in N'_0 union union_i F_i(R^n) with H^n(N'_0) = 0 and F_i Lipschitz; by the C^1 approximation theorem (Ch. 2, 1.5; its Whitney-extension core is SimonGMT Chapter02.exists_contDiff_one_extension_of_whitney) each F_i coincides, outside sets of arbitrarily small L^n-measure, with C^1 maps G_ij; by the area formula G_ij({J G_ij = 0}) is H^n-null, and each point of {J G_ij != 0} has a neighbourhood whose G_ij-image is an embedded n-dimensional C^1 submanifold (inverse function theorem); countably many such neighbourhoods suffice.) The cover can be disjointified into H^n-measurable pieces (SimonGMT Chapter03.simon_remark_1_3).
 (b) [Ch. 3, Rem. 1.8(1)] H^n restricted to M is sigma-finite (H^n(M cap K cap {theta > 1/j}) <= j integral_{M cap K} theta). By Lusin's theorem there are compact sets K_1, K_2, ... contained in M, increasing, with H^n(M minus union_i K_i) = 0 and theta restricted to K_i continuous; theta has a positive minimum c_i on K_i, so H^n(K_i) <= c_i^-1 integral_{K_i} theta < infinity. By the upper density theorem (Ch. 1, 3.6; SimonGMT Chapter01.simon_theorem_3_6) applied to the Radon measure mu restricted to (M minus K_i), there is an H^n-null set E_i such that r^-n mu(B_r(x) minus K_i) -> 0 as r -> 0 for every x in K_i minus E_i.
 (c) [Ch. 3, Thm. 1.6 '=>' for K_i] Fix i and put K_ij := K_i cap N_j minus union_{j' < j} N_j' (so H^n(K_i0) = 0). Fix j >= 1. N_j is covered by countably many open sets W in which N_j cap W is a C^1 graph of finite H^n-measure. By the upper density theorem for the finite measures H^n restricted to (K_i minus K_ij) and H^n restricted to ((N_j cap W) minus K_ij), for H^n-a.e. x in K_ij cap W both measures have zero n-dimensional density at x. Since N_j is C^1 at x, lim_{r -> 0} integral_{eta_{x,r}(N_j)} f dH^n = integral_{T_x N_j} f dH^n for f in C_c. Writing integral_{eta_{x,r}(K_i)} f = integral_{eta_{x,r}(N_j)} f - integral_{eta_{x,r}(N_j minus K_ij)} f + integral_{eta_{x,r}(K_i minus K_ij)} f and bounding the last two terms (for spt f in B_rho'(0)) by sup|f| r^-n H^n(B_{rho' r}(x) cap (N_j minus K_ij)) and sup|f| r^-n H^n(B_{rho' r}(x) cap (K_i minus K_ij)), which tend to 0, we get lim integral_{eta_{x,r}(K_i)} f dH^n = integral_{T_x N_j} f dH^n: the unweighted approximate tangent space T_x K_i (Def. 1.4) exists and equals T_x N_j. Hence T_x K_i exists for H^n-a.e. x in K_i.
 (d) [Ch. 3, Rem. 1.8(1)] Let x in K_i minus E_i be a point at which P := T_x K_i exists, and let f in C_c with spt f in B_rho'(0). By (*), integral_{eta_{x,r}(M)} f(z) theta(x + r z) dH^n(z) = r^-n integral_{K_i} f((w - x)/r) theta(w) dH^n(w) + r^-n integral_{M minus K_i} f((w - x)/r) dmu(w). The second term is at most sup|f| r^-n mu(B_{rho' r}(x) minus K_i) -> 0 by (b). In the first term |theta(w) - theta(x)| <= eps_r -> 0 uniformly for w in K_i cap B_{rho' r}(x) (continuity of theta on K_i), and r^-n H^n(K_i cap B_{rho' r}(x)) stays bounded (it converges to omega_n rho'^n by (c) applied to test functions squeezing the indicator of B_rho'(0)); hence the first term equals theta(x) integral_{eta_{x,r}(K_i)} f dH^n + o(1) -> theta(x) integral_P f dH^n. So P is the approximate tangent space of M w.r.t. theta at x.
 Since H^n(M minus union_i K_i) = 0 and every E_i is H^n-null, T_x(M, theta) exists for H^n-a.e. x in M. By 1(a),(b) this proves (ii): for mu-a.e. x there is an n-dimensional P with V.tangentProj x = P.starProjection.

4. Density (iii) (Ch. 3, Rem. 1.8(2)). Let x in M be such that P := T_x(M, theta) exists. For eps in (0,1) choose continuous compactly supported g_eps, h_eps : R^(n+l) -> [0,1] with g_eps = 1 on B_1(0), g_eps = 0 outside B_{1+eps}(0), h_eps = 1 on B_{1-eps}(0) and h_eps = 0 outside B^o_1(0). By (*), r^-n integral h_eps((w - x)/r) dmu <= r^-n mu(B_r(x)) <= r^-n integral g_eps((w - x)/r) dmu, and as r -> 0 the outer terms converge to theta(x) integral_P h_eps dH^n >= theta(x) omega_n (1 - eps)^n and to theta(x) integral_P g_eps dH^n <= theta(x) omega_n (1 + eps)^n (H^n on P is n-dimensional Lebesgue measure, H^n(P cap B_t(0)) = omega_n t^n). Letting eps -> 0, mu(B_r(x))/(omega_n r^n) -> theta(x) in (0, infinity); in extended reals, mu(B_r(x)) / ofReal(omega_n r^n) -> ofReal(theta(x)) as r -> 0+, i.e. V.HasDensity x (V.mult x). By step 3 and 1(a) this holds for mu-a.e. x.

5. Measurability (i). Let phi(t) := max{0, 1 - t} (t >= 0), c_0 := integral_{R^n} phi(|t|) dt > 0 and c_1 := (1/n) integral_{R^n} phi(|t|) |t|^2 dt > 0. For an n-dimensional subspace P with orthonormal basis tau_1, ..., tau_n, the isometric parametrization t -> sum_k t_k tau_k gives integral_P phi(|z|) dH^n(z) = c_0 and integral_P phi(|z|) z (x) z dH^n(z) = sum_{k,k'} (integral phi(|t|) t_k t_k' dt) tau_k (x) tau_k' = c_1 p_P (mixed moments vanish by the symmetry t_k -> -t_k, and integral phi(|t|) t_k^2 dt = c_1 for each k). For k >= 1 let W_k := {x : B_{2/k}(x) is contained in U} (open, as in step 2; U = union_k W_k) and for x in W_k set
 a_k(x) := k^n integral phi(k |w - x|) dmu(w), b_k(x) := k^(n+2) integral phi(k |w - x|) (w - x) (x) (w - x) dmu(w)
 (b_k(x) is a linear operator on R^(n+l)). The integrands are bounded, continuous in x and supported in B_{1/k}(x); for x within 1/k of a point x_0 in W_k these balls lie in the compact set B_{2/k}(x_0), contained in U, on which mu is finite, so a_k, b_k are continuous on W_k by dominated convergence. Define h_k(x) := (c_0/c_1) b_k(x)/a_k(x) if x in W_k and a_k(x) > 0, and h_k(x) := 0 otherwise; each h_k is Borel. If x in M and P = T_x(M, theta) exists, then x in W_k for large k and, by (*) with r = 1/k and the compactly supported continuous test functions z -> phi(|z|) and z -> phi(|z|) z_i z_j, a_k(x) -> theta(x) c_0 > 0 and b_k(x) -> theta(x) c_1 p_P; hence h_k(x) -> p_P = p_x by 1(b). By step 3 this convergence holds for mu-a.e. x. So p is the mu-a.e. limit of Borel, hence strongly measurable, maps into the finite-dimensional space of operators on R^(n+l), and is therefore mu-a.e. strongly measurable (Mathlib aestronglyMeasurable_of_tendsto_ae). This proves (i), and with steps 3 and 4 the theorem.

## Key steps

1. Reduce to H^n-a.e. statements on M and localize to pieces M_k on which theta is globally integrable
2. Cover M by C^1 submanifolds (Ch. 3, 1.2/1.3) and split by Lusin into compact pieces K_i with continuous theta
3. Upper density theorem gives T_x K_i = T_x N_j a.e. (Thm 1.6) and then the weighted tangent space T_x(M, theta) (Rem 1.8(1))
4. Squeezing test functions gives density = theta (Rem 1.8(2))
5. Second-moment quotients h_k are Borel and converge a.e. to p_x, so tangentProj is a.e. strongly measurable

## Reference use

### local-project

Queries:
- `diff GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean; diff GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Submission.lean`
- `rg -l 'allard52_' <snapshot>`
- `rg -l 'allard52_' .humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087 --include=*.json`
- `python: list dag.json nodes with lean_name and lean_statement (name-reservation check)`
- `rg -n 'theorem measurePreserving_homeomorphUnitSphereProd|def toSphere|theorem LipschitzWith.ae_differentiableAt|theorem measurable_fderiv\b|theorem Submodule.range_starProjection|theorem LipschitzOnWith.extend_pi|theorem ae_tendsto_average_norm_sub|theorem norm_fderiv_le_of_lipschitzOn|theorem LocallyIntegrableOn.integrableOn_isCompact|theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul|theorem uniqueDiffOn_convex|theorem aestronglyMeasurable_of_tendsto_ae' <snapshot>/mathlib/Mathlib`
- `rg -n 'range_starProjection|theorem aestronglyMeasurable_of_tendsto_ae|theorem LocallyIntegrableOn.integrableOn_compact_subset' <snapshot>/mathlib/Mathlib`
- `for pat in Campanato 'radial.*height' Allard monotonicity_formula upperDensity; do rg -l $pat <snapshot>/mathlib/Mathlib | wc -l; done`
- `rg -n '5.2|Allard|AllardRegularityTheorem|1/\(2n\+2\)|rate|gamma|γ' <snapshot>/project/GMT/Ch05/README.md`
- `grep -n 'def HasWeightedApproximateTangentSpaceAt|def CountablyRectifiable|def HasApproximateTangentSpaceAt|theorem HasWeightedApproximateTangentSpaceAt.unique' -A 25 .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rn 'theorem mul_simonHausdorff_le_of_le_dimensionalUpperDensity|theorem simon_theorem_3_6\b|theorem injective_area_formula_lipschitz_simon|theorem weighted_area_formula_lipschitz_injOn|def simonHausdorff|structure LpAnnularCorrection|def lpMeanCurvatureKappa' -A 22 .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -n 'theorem one_le_stationaryDensityReal_of_mem_support_lp|theorem simon_remark_1_3|theorem exists_contDiff_one_extension_of_whitney' .lake/packages/simongmt/Poincare/SimonGMT/{Chapter04/LpLowerDensity,Chapter03/DisjointCover,Chapter02/WhitneyExtension}.lean`
- `lean GMT/Ch05/Submission.lean -o /tmp/allard-decomp-v2/build/lib/lean/GMT/Ch05/Submission.olean (toolchains/lean-4.35.0-rc3-linux, LEAN_PATH from `lake env printenv LEAN_PATH`)`
- `LEAN_PATH=/tmp/allard-decomp-v2/build/lib/lean:<lake LEAN_PATH> lean /tmp/allard-decomp-v2/check/Types.lean (import GMT.Ch05.Submission; theorem Submission.<lean_name> : <lean_statement> := by sorry for all 8 children; #synth/#check instance probes)`
- `lean /tmp/allard-decomp-v2/check/Axioms.lean (#print axioms for the cited SimonGMT and Mathlib lemmas)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/TangentCone/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpAnnular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpLowerDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1/decomposition-review-receipt-v1.json`
- `/tmp/allard-decomp-v2/check/Types.lean`
- `/tmp/allard-decomp-v2/check/Axioms.lean`

Snapshot pins: project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). The workspace GMT/Ch05/Contract.lean and Submission.lean are byte-identical to the snapshot copies.

Names.
- `allard52_` has no match in the snapshot.
- In the run directory it occurs only in this node's rejected v1 decomposition, audit and receipt files.
- dag.json reserves other names, none of which collide: the 12 root conjunct names, plus rectifiableVarifold_ae_tangentProj_starProjection, divM_height_test_field_eq, hsNorm_starProjection_trace_identities and exists_smooth_cutoff_half_ball_grad_le in the tilt_excess_height_estimate branch.
- The eight bare names are therefore globally unique.

Mathlib. These searches return 0 files each: Campanato, radial.*height, Allard, monotonicity_formula, upperDensity. All eight children are therefore new. Usable lemmas found:
- toSphere (HaarToSphere.lean:51) and measurePreserving_homeomorphUnitSphereProd (HaarToSphere.lean:142);
- LipschitzWith.ae_differentiableAt (Rademacher.lean:385);
- measurable_fderiv (FDeriv/Measurable.lean:378);
- ae_tendsto_average_norm_sub (DensityTheorem.lean:150; Differentiation.lean:837);
- Submodule.range_starProjection (Projection/Basic.lean:302);
- LipschitzOnWith.extend_pi (Lipschitz.lean:344);
- norm_fderiv_le_of_lipschitzOn (FDeriv/Basic.lean:939);
- LocallyIntegrableOn.integrableOn_isCompact and integrableOn_compact_subset (LocallyIntegrable.lean:117,122);
- uniqueDiffOn_convex (TangentCone/Real.lean:79);
- lintegral_image_eq_lintegral_abs_det_fderiv_mul (Jacobian.lean:1183).

SimonGMT (pinned package, outside the snapshot).
- HasWeightedApproximateTangentSpaceAt (Chapter03/Rectifiable.lean:330) includes finrank P = n. It is a Bochner-integral limit over the blow-up weighted by θ(x + r•y). So V.tangentProj is everywhere 0 or a rank-n orthogonal projection, as the children use.
- HasWeightedApproximateTangentSpaceAt.unique (Rectifiable.lean:345) needs θ x ≠ 0.
- lpMeanCurvatureKappa = (p−n)/(4p) (Chapter04/LpMeanCurvature.lean:76) and LpAnnularCorrection (Chapter04/LpAnnular.lean:335) confirm the corrected monotonicity constants used in density_bounds. These are proved for SimonGMT's own varifold, so density_bounds re-derives them for the contract's RectifiableVarifold.
- mul_simonHausdorff_le_of_le_dimensionalUpperDensity and simon_theorem_3_6 (Chapter01/DensityComparison.lean:251,332) and injective_area_formula_lipschitz_simon (Chapter02/AreaLipschitz.lean:126) match their citations.

README (Ch05, lines 149-151) records that the δ-rate at a fixed γ needs an argument beyond the printed proof. This is Part III, isolated in radial_height.

Lean checks.
- Submission.lean compiled to a temporary olean; Types.lean (import GMT.Ch05.Submission) elaborated all eight lean_statement strings with only sorry warnings. Only density_bounds and graph_comparison changed type relative to v1: ∀ ℓ now comes after the existential constants.
- Instance probes: Prod.instMeasurableSpace, ContinuousLinearMap.instBorelSpace, Monoid.npow for ‖x‖^(n+2), and Submodule.starProjection on mapped graph planes.
- #print axioms gives only [propext, Classical.choice, Quot.sound] for: HasWeightedApproximateTangentSpaceAt.unique, simon_remark_1_3, injective_area_formula_lipschitz_simon, weighted_area_formula_lipschitz_injOn, simon_theorem_3_6, mul_simonHausdorff_le_of_le_dimensionalUpperDensity, exists_lpAnnularCorrection, one_le_stationaryDensityReal_of_mem_support_lp, measurePreserving_homeomorphUnitSphereProd, LipschitzWith.ae_differentiableAt, measurable_fderiv, ae_tendsto_average_norm_sub, LipschitzOnWith.extend_pi and Submodule.range_starProjection.
- Chapter02/WhitneyExtension has no built olean in the shared package cache, so its axioms were not printed. Its source contains no sorry, and it is cited only as a reference inside tangent_ae's proof.
