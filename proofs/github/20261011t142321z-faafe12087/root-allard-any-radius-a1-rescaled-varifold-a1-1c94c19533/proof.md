# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1`
- Child DAG node: `root.allard_any_radius-a1.rescaled_varifold-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

This is fact (Inv) of the parent proof. Notation: psi(x) := c + R x, phi(y) := R^-1 (y - c) = psi^-1(y), U' := psi^-1(U), M := V.carrier, theta := V.mult, mu := V.weight, H^n := μHE[n].

1. Scaling of H^n. psi is a similarity with ratio R and a homeomorphism of R^(n+l); U' is open. For every set A, H^n(psi(A)) = R^n H^n(A): Mathlib hausdorffMeasure_smul₀ gives μH[n](R A) = R^n μH[n](A), translations are isometries (IsometryEquiv.hausdorffMeasure_image), and μHE[n] is a constant multiple of μH[n] (euclideanHausdorffMeasure_def). Equivalently H^n(psi^-1(B)) = R^-n H^n(B) for every set B. In particular psi and phi map H^n-null sets to H^n-null sets, and for every nonnegative g and Borel E, the integral over psi^-1(E) of g(psi x) dH^n(x) equals R^-n times the integral over E of g dH^n.

2. Construction of V'. Take the carrier M' := psi^-1(M) and the multiplicity theta' := theta o psi, and check the fields of RectifiableVarifold. (i) M' is contained in U' because M is contained in U. (ii) M' is H^n-null-measurable: M differs from a Borel set B by a subset of an H^n-null Borel set Z, so M' differs from the Borel set psi^-1(B) by a subset of psi^-1(Z), which is H^n-null by step 1. (iii) M' is countably n-rectifiable: if M is contained in M_0 cup union_j range(F_j) with H^n(M_0) = 0 and F_j Lipschitz, then M' is contained in psi^-1(M_0) cup union_j range(phi o F_j), where H^n(psi^-1(M_0)) = R^-n H^n(M_0) = 0 and phi o F_j is Lipschitz. (iv) theta' > 0 on M'. (v) theta' is a.e.-measurable for H^n restricted to M': theta agrees with a measurable g off an H^n-null subset N of M, so theta' agrees with g o psi off psi^-1(N), which is H^n-null. (vi) For compact K contained in U', psi(K) is a compact subset of U, and by step 1 the integral over M' cap K of theta' dH^n equals R^-n times the integral over M cap psi(K) of theta dH^n, which is finite. The carrier and multiplicity identities hold by construction.

3. Weight. For every Borel set A, V'.weight(A) = integral over A cap M' of theta(psi x) dH^n(x) = R^-n integral over psi(A) cap M of theta dH^n = R^-n mu(psi(A)) = R^-n mu(phi^-1(A)) = R^-n (phi_# mu)(A), by step 1 and psi(A) = phi^-1(A). Measures that agree on Borel sets are equal, so V'.weight = (ENNReal.ofReal(R^n))^-1 • Measure.map phi mu (phi is continuous, hence measurable).

4. Support. Since phi is a homeomorphism, the support of phi_# mu is phi(spt mu) = psi^-1(spt mu), and multiplying by the positive finite constant R^-n does not change the support. Hence V'.support = U' cap psi^-1(spt mu) = psi^-1(U cap spt mu) = psi^-1(V.support).

5. Tangent projections. Fix x and r > 0. Then eta_{x,r}(M') = {r^-1 (z - x) : psi(z) in M} = {(R r)^-1 (m - psi(x)) : m in M} = eta_{psi(x), R r}(M) (blowUpMap x r y = r^-1 (y - x)); moreover theta'(x + r y) = theta(psi(x) + (R r) y) and theta'(x) = theta(psi(x)). Hence, for every f in C_c, the function r -> integral over eta_{x,r}(M') of f(y) theta'(x + r y) dH^n(y) is the corresponding function for (M, theta, psi x) composed with r -> R r, and r -> R r maps the filter 𝓝[>] 0 onto itself. Consequently, for every subspace P, HasWeightedApproximateTangentSpaceAt n M' theta' x P holds iff HasWeightedApproximateTangentSpaceAt n M theta (psi x) P holds (the dimension condition is the same). The two predicates on P are therefore equal (propositional and function extensionality), so the existence propositions in the definition of tangentProj are the same proposition and Classical.choose selects the same subspace; if no such P exists both projections are 0. Thus V'.tangentProj x = V.tangentProj (psi x) for every x.

6. Mean curvature. Assume V has generalized mean curvature H in U and put H'(x) := R H(psi x). (i) For compact K contained in U', step 3 gives integral over K of |H'| dV'.weight = R^(1-n) integral over psi(K) of |H| d mu < infinity, since psi(K) is a compact subset of U; so H' is locally integrable on U' for V'.weight. (ii) Let X' be C^1 with compact support and tsupport X' contained in U', and set X(y) := R X'(phi(y)). Then X is C^1 with compact support, tsupport X = psi(tsupport X') is contained in U, and DX(y) = DX'(phi(y)) by the chain rule. By step 5, div_M X(psi x) = trace(DX(psi x) o V.tangentProj(psi x)) = trace(DX'(x) o V'.tangentProj x) = div_{M'} X'(x). By step 3, the integral of a function g against V'.weight equals R^-n times the integral of g o phi against mu, and integrability is preserved in both directions, so the Bochner integrals correspond also when they vanish by non-integrability. Therefore
 integral div_{M'} X' dV'.weight = R^-n integral div_M X d mu = -R^-n integral X . H d mu = -R^-n integral R X'(phi y) . H(y) d mu(y) = -integral X'(x) . R H(psi x) dV'.weight(x) = -integral X' . H' dV'.weight.
 Hence V' has generalized mean curvature H' = (x -> R • H(c + R • x)) in U'.

## Key steps

1. psi is a similarity; H^n scales by R^n and null sets correspond
2. Carrier psi^-1(M) and multiplicity theta o psi satisfy all structure fields
3. Weight = R^-n phi_# mu by change of variables; the support is the preimage
4. Blow-ups of (M', theta') at x are those of (M, theta) at psi x with radius R r, so the tangent predicates and Classical.choose agree
5. Test fields X(y) = R X'(phi y) transport the first variation, giving mean curvature R H o psi

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
