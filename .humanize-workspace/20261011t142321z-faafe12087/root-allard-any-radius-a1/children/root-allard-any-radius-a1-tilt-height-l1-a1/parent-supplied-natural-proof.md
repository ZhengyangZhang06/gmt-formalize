# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1`
- Child DAG node: `root.allard_any_radius-a1.tilt_height_l1-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Lemma A of the parent proof (the L^1 form of the computation proving Simon Ch. 5, Lemma 2.1). Notation: mu := V.weight, p_x := V.tangentProj x, p_T := T.starProjection, |.| Hilbert-Schmidt norm (hsNorm), ||.|| operator norm (||A|| <= |A|), B_s(z) closed ball.

0. Integrability and a.e. facts. B_r(z) is a compact subset of U, so mu(B_r(z)) < infinity (field integrableOn_mult). The function x -> dist(x - z, T)^2 is continuous and bounded on B_r(z), hence integrable there; H is locally integrable on U (first conjunct of HasGeneralizedMeanCurvature), so |H| is integrable on the compact set B_r(z). By the child tangent_ae, x -> p_x is mu-a.e. strongly measurable and, for mu-a.e. x, p_x is the orthogonal projection onto an n-dimensional subspace; hence |p_x - p_T|^2 <= (|p_x| + |p_T|)^2 = 4n mu-a.e., and every integrand below is bounded, mu-measurable and supported in B_r(z), hence integrable. Finally mu(R^(n+l) minus spt mu) = 0 and mu(R^(n+l) minus U) = 0, so mu-a.e. x lies in spt V = U cap spt mu.

1. Cutoff. Fix phi in C^infinity(R, [0,1]) with phi = 1 on (-infinity, 1/2], phi = 0 on [1, infinity) and |phi'| <= 3 (possible since the transition interval has length 1/2 > 1/3). Put zeta(x) := phi(|x - z|/r). Then zeta is C^infinity (phi is constant near 0, so the non-smoothness of |x - z| at z is irrelevant), 0 <= zeta <= 1, zeta = 1 on B_{r/2}(z), zeta = 0 outside the open ball B^o_r(z), and |grad zeta| <= 3/r.

2. Test field. Let Q := I - p_T (projection onto the orthogonal complement of T), x' := Q(x - z), so |x'| = dist(x - z, T), and X(x) := zeta(x)^2 x'. X is C^infinity with compact support and tsupport X is contained in B_r(z), which is contained in U; so the first variation identity integral div_M X d mu = -integral X . H d mu holds (and X . H is integrable by step 0).

3. Divergence. DX(x) v = zeta^2 Q v + 2 zeta (grad zeta . v) x'. At every x where p_x is a rank-n orthogonal projection (mu-a.e.), div_M X(x) = trace(DX(x) o p_x) = zeta^2 trace(Q p_x) + 2 zeta (p_x grad zeta) . x' = zeta^2 s(x) + 2 zeta grad zeta . (p_x - p_T) x', where s(x) := (1/2)|p_x - p_T|^2. Indeed p_T x' = 0 gives p_x x' = (p_x - p_T) x'; and for rank-n orthogonal projections trace(Q p_x) = n - trace(p_T p_x), while |p_x - p_T|^2 = trace((p_x - p_T)^2) = 2n - 2 trace(p_T p_x).

4. Identity. Inserting step 3 into step 2: integral zeta^2 s d mu = -integral 2 zeta grad zeta . (p_x - p_T) x' d mu - integral zeta^2 x' . H d mu.

5. Absorption. |(p_x - p_T) x'| <= ||p_x - p_T|| |x'| <= |p_x - p_T| |x'| = sqrt(2 s) |x'|, and 2 sqrt(2 s) zeta |grad zeta| |x'| = 2 (zeta sqrt(s)/sqrt 2)(2 |grad zeta| |x'|) <= (1/2) zeta^2 s + 4 |grad zeta|^2 |x'|^2. Since integral zeta^2 s d mu is finite (step 0), step 4 gives (1/2) integral zeta^2 s d mu <= 4 integral |grad zeta|^2 |x'|^2 d mu + integral zeta^2 |x'| |H| d mu, i.e. integral zeta^2 s d mu <= 8 integral |grad zeta|^2 |x'|^2 d mu + 2 integral zeta^2 |x'| |H| d mu.

6. Conclusion. Since zeta = 1 on B_{r/2}(z) and s >= 0, (1/2) integral over B_{r/2}(z) of |p_x - p_T|^2 d mu <= integral zeta^2 s d mu. On the right of step 5 the integrands vanish outside B_r(z), |grad zeta|^2 <= 9/r^2, zeta <= 1, and |x'| = dist(x - z, T) <= h for mu-a.e. x in B_r(z) (such x lie in spt V cap B_r(z), step 0). Hence (1/2) integral over B_{r/2}(z) of |p_x - p_T|^2 d mu <= 72 r^-2 integral over B_r(z) of dist(x - z, T)^2 d mu + 2 h integral over B_r(z) of |H| d mu. Multiplying by 2 gives the claim: integral over B_{r/2}(z) of hsNormSq(p_x - p_T) d mu <= 144 (r^2)^-1 integral over B_r(z) of dist(x - z, T)^2 d mu + 4 h integral over B_r(z) of |H| d mu.

## Key steps

1. Integrability on the compact ball B_r(z) in U; mu-a.e. x lies in spt V and p_x is a rank-n projection (tangent_ae)
2. Test field X = zeta^2 p_{T^perp}(x - z) with a cutoff zeta, |grad zeta| <= 3/r
3. div_M X = zeta^2 (1/2)|p_x - p_T|^2 + 2 zeta grad zeta . (p_x - p_T) x'
4. First variation and Young absorption: integral zeta^2 s <= 8 integral |grad zeta|^2 |x'|^2 + 2 integral zeta^2 |x'| |H|
5. Insert zeta = 1 on B_{r/2}(z), |grad zeta| <= 3/r and |x'| <= h

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
