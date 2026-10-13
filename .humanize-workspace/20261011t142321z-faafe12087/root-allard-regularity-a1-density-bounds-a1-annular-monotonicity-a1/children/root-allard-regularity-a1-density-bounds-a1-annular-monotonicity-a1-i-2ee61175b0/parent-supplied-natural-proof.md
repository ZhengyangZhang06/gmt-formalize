# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1`
- Child DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.integrating_factor-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof (the integrating factor; Simon, Ch. 4, 4.3-4.4), stated for abstract functions. In the application, I = I_eps, E = E_eps and Q(t) = t^(-1) integral (r_x/t)(-phi_eps'(r_x/t)) nu dmu, which is J_eps'(t). The identity n I - t I' + t Q = -E is step 2(d).

Notation: Psi(t) := 1 + I(t)/t^n, G(t) := integral_0^t a (interval integral), Phi~(t) := exp(-G(t)) Psi(t). Fix 0 < s <= r < R; then [s, r] is contained in (0, R).

1. Continuity of a. Let t be in (0, R).
 - I is continuous at t, because it is differentiable there.
 - t^n > 0 and I(t) >= 0, so Psi(t) >= 1 > 0.
 - E is continuous at t.
 Hence a = E/t^(n+1)/Psi is continuous at t. In particular a is continuous on (0, R).

2. Integrability of a near 0. Let t be in (0, R).
 - On (0, t], a is continuous, hence measurable, and |a(tau)| <= M tau^(-beta) <= |M| tau^(-beta).
 - Since -beta > -1, tau -> tau^(-beta) is integrable on (0, t]: integral_0^t tau^(-beta) dtau = t^(1-beta)/(1-beta).
 - Hence a is integrable on (0, t], and G(t) is a finite real number. The value of a at the single point 0 is irrelevant.

3. Derivative of G. Let t be in (0, R).
 - a is integrable on [0, t], measurable on a neighbourhood of t (it is continuous on the open set (0, R)), and continuous at t.
 - By the fundamental theorem of calculus, G has derivative a(t) at t.
 - Consequently t -> exp(-G(t)) has derivative -a(t) exp(-G(t)) at t, and G is continuous on (0, R).

4. Derivative of Psi. For t in (0, R), t != 0, so the quotient rule gives
 Psi'(t) = I'(t)/t^n - n I(t) t^(n-1)/t^(2n) = I'(t)/t^n - n I(t)/t^(n+1) = (t I'(t) - n I(t))/t^(n+1).

5. Key identity.
 - By hypothesis t I'(t) - n I(t) = t Q(t) + E(t). So Psi'(t) = Q(t)/t^n + E(t)/t^(n+1).
 - Since Psi(t) != 0, a(t) Psi(t) = E(t)/t^(n+1). Hence Psi'(t) = Q(t)/t^n + a(t) Psi(t).

6. Derivative of Phi~. For t in (0, R), the product rule with steps 3 and 5 gives
 Phi~'(t) = -a(t) exp(-G(t)) Psi(t) + exp(-G(t)) (Q(t)/t^n + a(t) Psi(t)) = exp(-G(t)) Q(t)/t^n.

7. Conclusion.
 - The function t -> exp(-G(t)) Q(t)/t^n is continuous on [s, r]: G is continuous by step 3, Q by hypothesis, and t^n > 0. Hence it is interval integrable on [s, r].
 - Phi~ has this derivative at every point of [s, r].
 - By the fundamental theorem of calculus, Phi~(r) - Phi~(s) = integral_s^r exp(-G(t)) Q(t)/t^n dt, which is the claim.

## Key steps

1. a is continuous on (0, R) because Psi = 1 + I/t^n >= 1.
2. |a| <= M tau^(-beta) with beta < 1 makes a integrable on (0, t]. By the FTC, G(t) = integral_0^t a has G' = a on (0, R).
3. By the hypothesis identity, Psi' = (t I' - n I)/t^(n+1) = Q/t^n + E/t^(n+1) = Q/t^n + a Psi.
4. Phi~ = exp(-G) Psi has Phi~' = exp(-G) Q/t^n on (0, R).
5. The FTC on [s, r], with a continuous derivative, gives the identity.

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
