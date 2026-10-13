# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1`
- Child DAG node: `root.allard_any_radius-a1.tangent_ae-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 3, Lemma 1.2, Remark 1.3, Definition 1.7, Remark 1.8 and Theorem 1.9 (printed proofs), together with Ch. 1, Lusin's Theorem 1.17 and the Upper Density Theorem 3.6. This is fact (F1) of the parent proof; (c) is Remark 1.8(2). Notation: M := V.carrier, theta := V.mult, mu := V.weight (= theta H^n restricted to M), H^n := μHE[n], B_r(x) closed ball, eta_{x,r}(y) := r^-1 (y - x) (SimonGMT blowUpMap x r), omega_n := unitBallVolume n.

1. Null sets. For every set A, mu(A) = integral over A cap M of theta dH^n, and theta > 0 on M. Hence mu(R^(n+l) minus M) = 0, and a subset of M is mu-null iff it is H^n-null. It therefore suffices to prove (a) and (c) at H^n-a.e. point of M, and for (b) to exhibit a Borel map agreeing with V.tangentProj at H^n-a.e. point of M.

2. Radon property. For compact K contained in U, mu(K) = integral over M cap K of theta dH^n < infinity (field integrableOn_mult). Since U is open, every x in U has a closed ball around it contained in U; so mu is a Radon measure on U, and for small radii all blow-up integrals below only involve such balls (on which theta is integrable).

3. C^1 decomposition (Lemma 1.2, Remark 1.3). Since M is countably n-rectifiable, M is contained in N_0 cup N_1 cup N_2 cup ..., where H^n(N_0) = 0 and each N_j (j >= 1) is an embedded n-dimensional C^1 submanifold. [Proof of 1.2: each Lipschitz map F_j of Definition 1.1 agrees, off sets of arbitrarily small measure, with C^1 maps G_ij (C^1 approximation theorem, Ch. 2, 1.5); the image of the remaining L^n-null set is H^n-null because F_j is Lipschitz; by the area formula the image of {J G_ij = 0} is H^n-null; near a point where J G_ij is not 0, G_ij maps a small ball onto an embedded C^1 submanifold.] Put M_0 := M cap N_0 and M_j := (M cap N_j) minus (M_0 cup ... cup M_(j-1)). These are disjoint H^n-measurable sets with union M, H^n(M_0) = 0 and M_j contained in N_j.

4. Lusin (Remark 1.8(1)). Let (K_m) be an increasing exhaustion of U by compact sets. The H^n-measurable sets M_j cap K_m cap {theta >= 1/i} (i, m = 1, 2, ...) cover M_j up to an H^n-null set (theta > 0 on M and theta is H^n-a.e. equal to a measurable function on M) and have finite H^n-measure, at most i mu(K_m) < infinity. By Lusin's theorem (Ch. 1, 1.17) applied to theta on each of them, there are compact sets M_jk contained in M_j (k = 1, 2, ..., enumerating all the compact sets obtained) with H^n(M_j minus union_k M_jk) = 0 and theta restricted to M_jk continuous. As theta > 0 on the compact set M_jk, theta >= c_jk > 0 there, so H^n(M_jk) <= mu(M_jk)/c_jk < infinity.

5. Density zero of the complements. Fix j, k. The Upper Density Theorem (Ch. 1, 3.6) is applied below to finite Borel measures on R^(n+l); this suffices because upper densities at a point x only involve balls B_s(x) with s small. (i) Let W be an open ball with closure contained in U and nu_jk^W(A) := mu((A cap closure(W)) minus M_jk), a finite Borel measure (mu(closure(W)) < infinity) with nu_jk^W(M_jk) = 0; by 3.6, Theta^{*n}(nu_jk^W, x) = 0 for H^n-a.e. x in M_jk, and for x in M_jk cap W this upper density equals that of nu_jk(A) := mu(A minus M_jk). Countably many such balls W cover U, so Theta^{*n}(nu_jk, x) = 0 for H^n-a.e. x in M_jk. (ii) Cover N_j by countably many open sets W' such that N_j cap W' is the graph of a C^1 map over a bounded open subset of an n-plane with bounded derivative, so that H^n(N_j cap W') < infinity. The finite Borel measure A -> H^n((A cap N_j cap W') minus M_jk) gives measure 0 to M_jk, so by 3.6 its upper density vanishes at H^n-a.e. x in M_jk; for x in M_jk cap W' it coincides near x with H^n restricted to N_j minus M_jk. Hence Theta^{*n}(H^n restricted to N_j minus M_jk, x) = 0 for H^n-a.e. x in M_jk. Let E_jk be the union of the two exceptional sets; H^n(E_jk) = 0.

6. Blow-ups at good points. Let x be in M_jk minus E_jk, let P := T_x N_j be the classical tangent plane (dim P = n), and let f be in C_c(R^(n+l)) with f = 0 outside B_K(0). For r > 0 so small that B_{rK}(x) lies in a closed ball contained in U, the scaling H^n(eta_{x,r}(A)) = r^-n H^n(A) gives
 integral over eta_{x,r}(M) of f(y) theta(x + r y) dH^n(y) = r^-n integral f(eta_{x,r} z) d mu(z) = r^-n integral over M_jk of f(eta_{x,r} z) theta(z) dH^n(z) + r^-n integral f(eta_{x,r} z) d nu_jk(z).
 The last term is at most sup|f| r^-n nu_jk(B_{rK}(x)), which tends to 0 by 5(i). In the first term, |theta(z) - theta(x)| <= w(rK) for z in M_jk cap B_{rK}(x), where w(t) -> 0 is the modulus of continuity of theta restricted to M_jk at x, while r^-n H^n(M_jk cap B_{rK}(x)) <= r^-n H^n(N_j cap B_{rK}(x)) stays bounded. Hence the first term equals theta(x) r^-n integral over M_jk of f(eta_{x,r} z) dH^n(z) + o(1) = theta(x) [integral over eta_{x,r}(N_j) of f dH^n - r^-n integral over N_j minus M_jk of f(eta_{x,r} z) dH^n(z)] + o(1). The subtracted integral is at most sup|f| r^-n H^n((N_j minus M_jk) cap B_{rK}(x)) -> 0 by 5(ii), and the integral over eta_{x,r}(N_j) of f dH^n tends to the integral over P of f dH^n, because near x the submanifold N_j is the graph of a C^1 map over P with zero derivative at x, so eta_{x,r}(N_j) converges to P in C^1 on B_K(0) (area formula). Therefore the left side tends to theta(x) times the integral over P of f dH^n for every f in C_c, i.e. HasWeightedApproximateTangentSpaceAt n M theta x P holds, and finrank P = n.

7. Proof of (a). By steps 3-6, the set of x in M at which no such P exists is contained in M_0 cup union_j (M_j minus union_k M_jk) cup union_{j,k} E_jk, which is H^n-null, hence mu-null by step 1. At a good point x we have theta(x) > 0 (x is in M), and weighted approximate tangent spaces are unique where theta is not 0 (SimonGMT HasWeightedApproximateTangentSpaceAt.unique). Hence the subspace selected by Classical.choose in the definition of V.tangentProj is P, and V.tangentProj x = P.starProjection.

8. Proof of (b). Enumerate the pairs (j,k) and let M'_jk := M_jk minus the union of the earlier M_j'k'; these sets are Borel and pairwise disjoint. Define G(x) := orthogonal projection onto T_x N_j for x in M'_jk, and G(x) := 0 elsewhere. Since x -> T_x N_j is continuous on the C^1 submanifold N_j, G is Borel measurable, and by step 7, G(x) = V.tangentProj x at H^n-a.e. point of M, hence mu-a.e. The values lie in the finite-dimensional normed space of continuous linear maps, so V.tangentProj is mu-a.e. strongly measurable (AEStronglyMeasurable for V.weight).

9. Proof of (c) (Remark 1.8(2)). Let x and P be as in step 7, and 0 < eps < 1. Choose f_eps, g_eps in C_c(R^(n+l), [0,1]) with f_eps = 1 on B_1(0), f_eps = 0 outside B_{1+eps}(0), g_eps = 1 on B_{1-eps}(0) and g_eps = 0 outside the open unit ball. By the identity of step 6, r^-n mu(B_r(x)) <= r^-n integral f_eps(eta_{x,r} z) d mu(z), which tends to theta(x) times the integral over P of f_eps, at most theta(x) omega_n (1+eps)^n; and r^-n mu(B_r(x)) >= r^-n integral g_eps(eta_{x,r} z) d mu(z), which tends to theta(x) times the integral over P of g_eps, at least theta(x) omega_n (1-eps)^n (H^n restricted to the n-plane P is Lebesgue measure, so H^n(P cap B_s(0)) = omega_n s^n). Letting eps -> 0 gives mu(B_r(x))/(omega_n r^n) -> theta(x) as r -> 0+. All quantities are finite and nonnegative, so V.weight(closedBall x r)/ENNReal.ofReal(omega_n r^n) converges to ENNReal.ofReal(theta x), i.e. V.HasDensity x (V.mult x) holds. By step 7 this is the case for mu-a.e. x.

## Key steps

1. mu-null subsets of M are exactly the H^n-null ones (theta > 0); mu is Radon on U
2. Cover M by embedded C^1 submanifolds N_j up to an H^n-null set (Lemma 1.2, Remark 1.3)
3. Lusin gives compact M_jk with theta continuous; the upper density theorem kills the density of M minus M_jk and of N_j minus M_jk
4. At good points the blow-ups converge to theta(x) H^n on T_x N_j: the weighted tangent exists and, by uniqueness, equals the Classical.choose in tangentProj
5. The Borel map x -> p_{T_x N_j} on the pieces gives a.e. strong measurability
6. Test functions squeezing the unit ball give Theta^n(mu, x) = theta(x)

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean`
- `rg -l 'any_radius_' <snapshot>/project`
- `python3 -I scan of every lean_name field in dag.json and nodes/*/*.json of this run (reservation check)`
- `rg -l -t lean 'Campanato' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem measurePreserving_homeomorphUnitSphereProd|^def toSphere|theorem toSphere_apply_univ' <snapshot>/mathlib/Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`
- `rg -n 'lemma toSphere|theorem toSphere|def volumeIoiPow' <snapshot>/mathlib/Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`
- `rg -n 'theorem ae_tendsto_average_norm_sub' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `rg -n 'protected def vitaliFamily|theorem tendsto_filterAt' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `rg -n 'hausdorffMeasure_smul' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'localInverse' <snapshot>/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `rg -n 'theorem volume_closedBall' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `rg -n 'theorem MeasurableSet.image_of_continuousOn_injOn' <snapshot>/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `rg -n 'norm_image_sub_le_of_norm_fderivWithin_le' <snapshot>/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `rg -n 'tendsto_log_mul_rpow_nhdsGT_zero' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`
- `rg -n 'Measure.support|support_mem_ae' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `grep -n 'def HasWeightedApproximateTangentSpaceAt|def blowUpMap|def CountablyRectifiable|theorem HasWeightedApproximateTangentSpaceAt.unique' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n 'def lpMeanCurvatureKappa|structure LpAnnularCorrection|exists_lpAnnularCorrection|one_le_stationaryDensityReal_of_mem_support_lp' .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean Chapter04/LpAnnular.lean Chapter04/LpLowerDensity.lean; rg -c '\bsorry\b' .lake/packages/simongmt/Poincare/SimonGMT`
- `lake build GMT.Ch05.Submission in the scratch copy /tmp/anyrad-v2/proj of the pinned project (packages symlinked to the workspace .lake/packages)`
- `lake env lean Checks/Types.lean (import GMT.Ch05.Submission; namespace GMT.Ch05; the 12 child types)`
- `lake env lean Checks/Final.lean (12 child types + ParentSkeleton.parent_assembly + RateSkeleton.rate_skeleton + 6.1 shape check)`
- `lake env lean Checks/Inst.lean (set_option pp.explicit true; #check of the weight smul, real scalars and rpow expressions)`
- `lake env lean Checks/Axioms.lean (#print axioms of the cited library results)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpAnnular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpLowerDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1/decomposition-audit-v1.json`
- `/tmp/anyrad-v2/proj/Checks/Types.lean`
- `/tmp/anyrad-v2/proj/Checks/Final.lean`
- `/tmp/anyrad-v2/proj/Checks/Inst.lean`
- `/tmp/anyrad-v2/proj/Checks/Axioms.lean`

Snapshot and reservations
- Pinned at project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json).
- Its Contract.lean and Submission.lean are byte-identical to the workspace copies (cmp).
- No-match results: 'any_radius_' occurs in 0 snapshot project files; within the run it appears only in this node's own v1 proposal. 'Campanato' matches 0 Mathlib files, so campanato is proved from scratch.
- dag.json and all nodes/*/*.json reserve only: the 12 first-level names, the tilt_excess_height_estimate children (rectifiableVarifold_ae_tangentProj_starProjection, divM_height_test_field_eq, hsNorm_starProjection_trace_identities, exists_smooth_cutoff_half_ball_grad_le), and the aal_/allard52_/lgc_/lip_approx_/w12_ proposal names. No any_radius_* name collides.

Mathlib in the snapshot, by child
- radial_height (polar coordinates): measurePreserving_homeomorphUnitSphereProd (Constructions/HaarToSphere.lean:142), toSphere (:51), toSphere_apply_univ (:87), volumeIoiPow (:113).
- graph_comparison (Besicovitch differentiation): VitaliFamily.ae_tendsto_average_norm_sub (Covering/Differentiation.lean:837), with Besicovitch.vitaliFamily (Covering/Besicovitch.lean:1021) and tendsto_filterAt (:1060). It needs a measure that is locally finite on the whole space, hence mu restricted to B_rho(0).
- rescaled_varifold: Measure.hausdorffMeasure_smul₀ (Measure/Hausdorff.lean:753).
- patching: HasStrictFDerivAt.localInverse and to_localInverse (Calculus/InverseFunctionTheorem/FDeriv.lean:149).
- campanato: InnerProductSpace.volume_closedBall (Measure/Lebesgue/VolumeOfBalls.lean:354; EuclideanSpace version :324).
- Shared tools:
  - MeasurableSet.image_of_continuousOn_injOn (Constructions/Polish/Basic.lean:821);
  - Convex.norm_image_sub_le_of_norm_fderivWithin_le (Calculus/MeanValue.lean:484);
  - tendsto_log_mul_rpow_nhdsGT_zero (SpecialFunctions/Pow/Asymptotics.lean:401), for the delta^(1/4)|log delta| thresholds;
  - Measure.support and support_mem_ae (Measure/Support.lean).

Pinned SimonGMT package (outside the snapshot; rg finds 0 sorry)
- HasWeightedApproximateTangentSpaceAt (Chapter03/Rectifiable.lean:330) uses Bochner blow-up integrals over blowUpMap x r '' M (:96). Its uniqueness where theta != 0 (:345) justifies rescaled_varifold's exact tangent transport and tangent_ae's identification of tangentProj.
- monotonicity_bounds uses the corrected monotonicity:
  - lpMeanCurvatureKappa = (p-n)/(4p) (Chapter04/LpMeanCurvature.lean:76);
  - LpAnnularCorrection (LpAnnular.lean:335);
  - exists_lpAnnularCorrection and its _of_memLp variant (:358, :407);
  - one_le_stationaryDensityReal_of_mem_support_lp (LpLowerDensity.lean:43).

  These are stated for Chapter04.RectifiableVarifold, so the bridge via tangent_ae is spelled out.

Lean checks
- GMT.Ch05.Submission was built in a scratch copy of the pinned project. All 12 child types elaborate after 'import GMT.Ch05.Submission' in namespace GMT.Ch05.
- Three skeletons type-check, with only routine glue left as sorry:
  - the parent assembly (children + AllardRegularityTheorem + ConicalApproximationTheorem + TiltExcessDecayTheorem gives AllardRegularityAnyRadius);
  - graph_rate, with the C_II/C_III normalisation proved;
  - a shape check of 6.1.
- pp.explicit shows Measure.instSMul (ENNReal) and WithLp.instSMul (real scalars).
- #print axioms of every cited library result gives only propext, Classical.choice and Quot.sound.
