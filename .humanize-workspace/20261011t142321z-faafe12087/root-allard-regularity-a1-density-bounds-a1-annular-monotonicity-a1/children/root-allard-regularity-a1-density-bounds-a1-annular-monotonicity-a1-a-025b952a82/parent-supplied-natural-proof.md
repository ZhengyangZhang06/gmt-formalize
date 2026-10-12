# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1`
- Child DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.annular_tonelli-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 8 of the parent proof (Tonelli's theorem and the bound h_eps(c) >= c^(-n) for c in (s, r] with eps <= c/s - 1), for one fixed cutoff. The parent's substitution u = c/t is replaced by the equivalent fundamental-theorem-of-calculus computation in step 6. All other steps are the parent's.

Notation:
- r_x := |x - y| and phi' := deriv phi;
- B := closedBall y ((1+eps) r);
- A := closedBall y r minus ball y ((1+eps) s) = {x : (1+eps) s <= r_x <= r};
- B°_R := ball y R.
Since (1+eps) r < R, B is contained in B°_R, and A is contained in B.

1. Facts on phi.
 - phi is nonincreasing and differentiable, so phi' <= 0 everywhere.
 - phi is constant on (-infinity, 1) and on (1+eps, infinity), so phi' = 0 there.
 - Let C := max over [1, 1+eps] of |phi'|; it is finite because phi' is continuous. Then |phi'| <= C everywhere.

2. A measurable version of w.
 - By hypothesis there is a strongly measurable w_0 with w_0 = w mu-a.e. on B°_R.
 - Put w~(x) := min(max(w_0(x), 0), 1) for x in B°_R, and w~(x) := 0 otherwise.
 - Then w~ is measurable and 0 <= w~ <= 1 everywhere. Also w~ = w mu-a.e. on B°_R, because 0 <= w <= 1 mu-a.e. there.

3. The kernel. For c >= 0 and t > 0 let k(c, t) := (c/t^2)(-phi'(c/t)) >= 0.
 - k is continuous on [0, infinity) x (0, infinity).
 - If c > (1+eps) t, then c/t > 1 + eps and k(c, t) = 0.
 - For t in [s, r] and c >= 0: k(c, t) <= ((1+eps) r/s^2) C =: C'.

4. Rewriting Q. Let t be in [s, r].
 - The integrand (r_x/t) phi'(r_x/t) w(x) vanishes when r_x > (1+eps) t, in particular outside B.
 - On B, which lies in B°_R, it agrees mu-a.e. with (r_x/t) phi'(r_x/t) w~(x).
 - Hence Q(t) = -t^(-1) integral (r_x/t) phi'(r_x/t) w~(x) dmu = integral k(r_x, t) w~(x) dmu, and 0 <= k(r_x, t) w~(x) <= C' 1_B(x).

5. Fubini.
 - Consider K(t, x) := t^(-n) k(r_x, t) w~(x) on [s, r] x R^(n+l). It is measurable: a function continuous in (t, x) times a measurable function of x.
 - K is nonnegative and bounded by s^(-n) C' 1_B(x). It vanishes for x outside B, because there r_x > (1+eps) r >= (1+eps) t (step 3).
 - Since mu(B) <= mu(B_R(y)) < infinity, K is integrable for (Lebesgue measure on [s, r]) x mu.
 - By Fubini's theorem and step 4: integral_s^r Q(t)/t^n dt = integral_s^r (integral K(t, x) dmu(x)) dt = integral w~(x) h(r_x) dmu(x), where h(c) := integral_s^r t^(-n) k(c, t) dt >= 0. Moreover h(r_x) = 0 for x outside B.

6. Lower bound for h. Let c be in [(1+eps) s, r], so c > 0.
 - On (0, infinity), the function t -> phi(c/t) has the continuous derivative phi'(c/t)(-c/t^2) = k(c, t).
 - By the fundamental theorem of calculus, integral_s^r k(c, t) dt = phi(c/r) - phi(c/s) = 1 - 0 = 1, because c/r <= 1 and c/s >= 1 + eps.
 - If k(c, t) != 0, then phi'(c/t) != 0, so c/t >= 1 by step 1. Then t <= c and t^(-n) >= c^(-n).
 - Hence t^(-n) k(c, t) >= c^(-n) k(c, t) for all t in [s, r], and h(c) >= c^(-n) integral_s^r k(c, t) dt = c^(-n).
 - Equivalently, with u = c/t, h(c) = integral_(c/r)^(c/s) (u/c)^n (-phi'(u)) du >= c^(-n) integral_1^(1+eps) (-phi'(u)) du = c^(-n), since [1, 1+eps] lies in [c/r, c/s].

7. Comparison on A.
 - A is contained in B, hence in B°_R, so w = w~ mu-a.e. on A. Therefore the lower integral over A of ofReal(w/r_x^n) dmu equals the lower integral over A of ofReal(w~/r_x^n) dmu.
 - For x in A, c := r_x lies in [(1+eps) s, r]. By step 6 and w~ >= 0, w~(x)/r_x^n <= w~(x) h(r_x).
 - So the lower integral over A of ofReal(w~/r_x^n) dmu is at most the lower integral over A of ofReal(w~(x) h(r_x)) dmu. That is at most the lower integral over R^(n+l) of ofReal(w~(x) h(r_x)) dmu.

8. Conclusion.
 - The function x -> w~(x) h(r_x) is nonnegative and measurable; h is continuous on [0, infinity) as a parameter integral of a continuous integrand over the compact interval [s, r].
 - It is integrable, being bounded by (r - s) s^(-n) C' 1_B.
 - Hence its lower integral of ofReal equals ofReal(integral w~(x) h(r_x) dmu), which is ofReal(integral_s^r Q(t)/t^n dt) by step 5.
 - Combined with step 7, this gives the claim.

## Key steps

1. phi' <= 0, phi' = 0 off [1, 1+eps], and |phi'| <= C.
2. Replace w by a measurable w~ with values in [0, 1], equal to w mu-a.e. on ball y R.
3. Q(t) = integral k(r_x, t) w~ dmu with k(c, t) = (c/t^2)(-phi'(c/t)) >= 0, which vanishes for c > (1+eps)t.
4. Fubini: integral_s^r Q(t)/t^n dt = integral w~(x) h(r_x) dmu, where h(c) = integral_s^r t^(-n) k(c, t) dt.
5. For c in [(1+eps)s, r]: integral_s^r k(c, t) dt = phi(c/r) - phi(c/s) = 1, and t^(-n) >= c^(-n) where k != 0. So h(c) >= c^(-n).
6. On A, ofReal(w/r_x^n) <= ofReal(w~ h(r_x)) a.e. The lower integral of the nonnegative integrable function w~ h(r_x) is ofReal of its integral.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean`
- `grep -rn -E 'allard52_am_|allard52_annular_monotonicity|aal_curvature_pairing_holder_bound' <snapshot>/project (exit 1); grep -rln -E 'allard52_am_|allard52_annular_monotonicity|aal_curvature_pairing_holder_bound' --include=*.lean <snapshot>/mathlib/Mathlib (exit 1)`
- `grep -n -E '^theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le|^theorem continuousAt_of_dominated|^theorem integral_hasDerivAt_right|^theorem integral_eq_sub_of_hasDerivAt|^theorem integral_integral_swap|^theorem lintegral_liminf_le|^theorem tendsto_integral_filter_of_dominated_convergence|^theorem integral_rpow|^theorem intervalIntegrable_rpow|^theorem ofReal_integral_eq_lintegral_ofReal|^theorem setLIntegral_iUnion_of_directed|^theorem starProjection_orthogonal_val|^theorem norm_starProjection_apply_le|^theorem LocallyIntegrableOn.integrableOn_compact_subset|^theorem one_of_one_le|^theorem zero_of_nonpos|^protected theorem monotone|^protected theorem contDiff|^theorem integral_congr_ae|^theorem integral_mul_le_Lp_mul_Lq_of_nonneg' over the snapshot Mathlib files listed in files`
- `grep -rn -E 'theorem abs_exp_sub_one_le|lemma trace_smulRight|MonotoneOn.tendsto_nhdsGT' <snapshot>/mathlib/Mathlib/Analysis/Complex/Exponential.lean <snapshot>/mathlib/Mathlib/LinearAlgebra/Trace.lean <snapshot>/mathlib/Mathlib/Topology/Order/Monotone.lean`
- `python3 over dag.json: (id, lean_name, status, candidate_commit) for all 319 nodes; lean_statement of curvature_holder-a1, radial_first_variation-a1, monotonicity_core-a1, cutoff_squeeze-a1 and its 4 children, ted lp_monotonicity children, local_monotonicity-a1, lp_corrected_mass_ratio_monotoneOn, radial_cutoff_first_variation_eq and the density_bounds-a1 siblings`
- `git show 4c0fc30d6a1cd4ba43b449f2e51583e4e473c461:GMT/Ch05/Submission.lean (dohr_local_monotonicity proof structure); git show a86f40226e595267d72cfbfaf8d5fdbfa472219b:GMT/Ch05/Submission.lean (accepted aal_curvature_pairing_holder_bound)`
- `toolchains/lean-4.35.0-rc3-linux/bin/lean GMT/Ch05/Submission.lean -o /tmp/am-decomp/build/lib/GMT/Ch05/Submission.olean (LEAN_PATH = /tmp/am-decomp/build/lib plus lake-packages-25730c7c/*/.lake/build/lib/lean)`
- `LEAN_PATH=<same> lean /tmp/am-decomp/check/Avail.lean; Types.lean; Assembly.lean; AssemblyAx.lean; FixedSkel.lean; LimitSkel.lean; HolderAccepted.lean; MeasTest5.lean`
- `python3 -I: verifier/lean_contract.py validate_lean_statement on the 8 child types; byte comparison of the reused holder type with dag.json and of the parent type with dag.json and parent-child-handoff.json`
- `sed -n 375,570p book/chapter-04.txt (Simon Ch. 4, 3.16-3.17 and 4.1-4.9)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Complex/Exponential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-audit-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-lp-monotonicity-a1-curvature-holder-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-lp-monotonicity-a1-curvature-holder-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/tmp/am-decomp/check/Avail.lean`
- `/tmp/am-decomp/check/Types.lean`
- `/tmp/am-decomp/check/Assembly.lean`
- `/tmp/am-decomp/check/AssemblyAx.lean`
- `/tmp/am-decomp/check/FixedSkel.lean`
- `/tmp/am-decomp/check/LimitSkel.lean`
- `/tmp/am-decomp/check/HolderAccepted.lean`

Pins. Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Contract.lean and Submission.lean are byte-identical to the snapshot copies.

Names.
- No snapshot project or Mathlib file mentions allard52_am_*, allard52_annular_monotonicity or aal_curvature_pairing_holder_bound (grep exit 1).
- None of the seven new names is reserved in dag.json (319 nodes).
- aal_curvature_pairing_holder_bound is the comparator-accepted node root.affine_approximation-a1.lp_monotonicity-a1.curvature_holder-a1 (candidate a86f40226e). The proposed type is byte-identical to its frozen lean_statement. Its accepted proof recompiles here (HolderAccepted.lean) using only propext, Classical.choice and Quot.sound.
- Related nodes cannot be reused under their names. aal_radial_first_variation_identity and radial_cutoff_first_variation_eq assume tangent planes mu-a.e. on all of U, not only on the ball. aal_monotonicity_of_radial_identity, the aal_cfs_* nodes and the ted_lpm_* nodes are not accepted and use R < S radii. dohr_local_monotonicity has no conical term and no decay rate.

Mathlib. All tools the children need are in the import closure of GMT.Ch05.Submission (#check in Avail.lean). Locations in the snapshot:
- ParametricIntegral.lean:286 hasDerivAt_integral_of_dominated_loc_of_deriv_le
- Bochner/Basic.lean:458 continuousAt_of_dominated; :301 integral_congr_ae; :739 ofReal_integral_eq_lintegral_ofReal
- FundThmCalculus.lean:725 integral_hasDerivAt_right; :1148 integral_eq_sub_of_hasDerivAt
- Integral/Prod.lean:478 integral_integral_swap
- Lebesgue/Add.lean:216 lintegral_liminf_le'
- Lebesgue/Basic.lean:668 setLIntegral_iUnion_of_directed
- DominatedConvergence.lean:67 tendsto_integral_filter_of_dominated_convergence (plus the interval version)
- Integrals/Basic.lean:146 integral_rpow; Integrability/Basic.lean:47 intervalIntegrable_rpow'
- Complex/Exponential.lean:533 Real.abs_exp_sub_one_le
- Projection/Basic.lean:203 starProjection_orthogonal_val; :411 norm_starProjection_apply_le
- Trace.lean:272 trace_smulRight
- Topology/Order/Monotone.lean:485 MonotoneOn.tendsto_nhdsGT
- SmoothTransition.lean:161-222 smoothTransition lemmas
- LocallyIntegrable.lean:122 LocallyIntegrableOn.integrableOn_compact_subset

Lean checks (Lean v4.35.0-rc3).
- Types.lean: all eight child types elaborate after import GMT.Ch05.Submission in namespace GMT.Ch05, with only sorry warnings. All pass validate_lean_statement.
- Assembly.lean: proves the exact frozen allard52_annular_monotonicity type (byte-identical to dag.json and the handoff) from radial_identity, cutoff_limit and center_density.
- AssemblyAx.lean: with the children as axioms, #print axioms lists propext, Classical.choice, Quot.sound, allard52_am_radial_identity, allard52_am_cutoff_limit and allard52_am_center_density.
- FixedSkel.lean: a skeleton of allard52_am_fixed_cutoff that instantiates holder_bound, cutoff_calculus, integrating_factor and annular_tonelli typechecks. The remaining sorries are routine integrability and algebra.
- LimitSkel.lean: a skeleton of allard52_am_cutoff_limit typechecks. It builds C^1 cutoffs from smoothTransition and instantiates fixed_cutoff for every k, with I, E, a given by rfl and the radial hypothesis at T = 1 + eps_k.
- No Matrix/IsUnit or other instance-sensitive inline construction occurs.

Source. The local copy of Simon Ch. 4 (book/chapter-04.txt, 3.16-3.17 and 4.1-4.9) follows the same structure:
- first variation with radial cutoffs;
- the Hoelder bound with a^(1-1/p) <= 1 + a giving |F0| <= 2 Lambda R^(-1)(rho/R)^(-n/p);
- the integrating factor;
- the limit eps -> 0, giving the annular identity 4.7 and the monotonicity 4.8.
