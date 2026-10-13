# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1`
- Child DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.fixed_cutoff-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2(c), 2(d), 3 and 4 of the parent proof, and the per-cutoff part of step 8 (Simon, Ch. 4, 4.1-4.4). They are stated for one cutoff phi = phi_eps, with an abstract measure mu, curvature H and weight w; in the application w = nu. The proof uses the sibling lemmas holder_bound (aal_curvature_pairing_holder_bound), cutoff_calculus, integrating_factor and annular_tonelli.

Notation:
- r_x := |x - y|, phi' := deriv phi, B_t := closedBall y t;
- kappa := (p - n)/(4p), alpha' := 1 - n/p;
- R' := R/(1+eps), so (1+eps) t < R iff t < R';
- Q_R := lower integral over B_R of |H|^p dmu;
- b(t) := 2 kappa Lambda R^(-1) (t/R)^(-n/p);
- Q(t) := -(integral (r_x/t) phi'(r_x/t) w(x) dmu)/t and I'(t) := -(integral (r_x/t) phi'(r_x/t) dmu)/t;
- G(t) := integral_0^t a and Phi~(t) := exp(-G(t))(1 + I(t)/t^n).

0. Constants. 1 <= n < p gives p > 1, 0 < n/p < 1, 0 < alpha' < 1 and kappa > 0. Also 2 kappa/alpha' = 2 (p-n)/(4p) * p/(p-n) = 1/2.

1. Cutoff facts.
 - phi is nonincreasing with phi = 1 on (-infinity, 1] and phi = 0 on [1+eps, infinity). So 0 <= phi <= 1, phi' <= 0, and phi' = 0 on (1+eps, infinity).
 - Hence, for t > 0, phi(r_x/t) = 0 and phi'(r_x/t) = 0 whenever r_x > (1+eps) t.

2. The L^p norm.
 - Let K := (ofReal(R^(p-n)) Q_R)^(1/p). By hypothesis K <= ofReal(kappa Lambda) < infinity.
 - As 1/p > 0, ofReal(R^(p-n)) Q_R < infinity. As ofReal(R^(p-n)) > 0, Q_R < infinity.
 - Then K = ofReal((R^(p-n) Q_R.toReal)^(1/p)) = ofReal(R^((p-n)/p) N), where N := (Q_R.toReal)^(1/p) >= 0.
 - So R^((p-n)/p) N <= kappa Lambda, i.e. N <= kappa Lambda R^(n/p - 1).
 - For 0 < t_1 <= R, the lower integral over B_(t_1) of |H|^p is at most Q_R < infinity, and the 1/p-th power of its toReal is at most N.

3. Integrability.
 (a) For 0 < S < R, B_S lies in ball y R. So w is a.e.-strongly measurable for mu restricted to B_S and |w| <= 1 mu-a.e. on B_S. As mu(B_S) <= mu(B_R) < infinity, w is integrable on B_S.
 (b) The constant 1 is integrable on B_R. The function x -> (x - y).H(x) is integrable on B_R: it is a.e.-strongly measurable there and bounded by R|H|.
 (c) For t in (0, R'), the functions phi(r_x/t), (r_x/t) phi'(r_x/t) and (r_x/t) phi'(r_x/t) w(x) are mu-integrable. They vanish outside B_((1+eps)t), which lies in ball y R. On that ball they are bounded (phi and u phi'(u) are bounded on [0, 1+eps], and |w| <= 1 a.e.) and a.e.-strongly measurable, and mu(B_((1+eps)t)) < infinity.

4. Regularity from cutoff_calculus. Fix t in (0, R') and put S := ((1+eps)t + R)/2, so (1+eps) t < S < R. Apply cutoff_calculus with T := 1 + eps > 0:
 (a) with f = 1 (integrable on B_S by 3(b)): I(s) = integral phi(r_x/s) dmu has derivative I'(t) at t; in particular I is continuous at t;
 (b) with f(x) = (x - y).H(x) (integrable on B_S by 3(b)): E is continuous at t;
 (c) with f = w (integrable on B_S by 3(a)): s -> integral (r_x/s) phi'(r_x/s) w(x) dmu is continuous at t. Since t != 0, Q is continuous at t.

5. The identity n I - t I' + t Q = -E on (0, R'). Let t be in (0, R').
 - The radial identity at rho = t gives integral (n phi(r_x/t) + (r_x/t) phi'(r_x/t)(1 - w(x))) dmu = -E(t).
 - By 3(c) the integral splits: n I(t) + integral (r_x/t) phi'(r_x/t) dmu - integral (r_x/t) phi'(r_x/t) w dmu = -E(t).
 - As t I'(t) = -integral (r_x/t) phi'(r_x/t) dmu and t Q(t) = -integral (r_x/t) phi'(r_x/t) w dmu, this is n I(t) - t I'(t) + t Q(t) = -E(t).

6. Signs. Let t be in (0, R').
 - I(t) >= 0, because phi >= 0.
 - Q(t) >= 0: the integrand (r_x/t) phi'(r_x/t) w(x) is 0 outside B_((1+eps)t). Mu-a.e. on B_((1+eps)t), which lies in ball y R, it is a product of r_x/t >= 0, phi' <= 0 and w >= 0, hence <= 0.

7. Hoelder. Let t be in (0, R') and t_1 := (1+eps) t <= 2t (as eps <= 1). Apply holder_bound with p, mu, H, psi(x) := phi(r_x/t), y and radius t_1. Its hypotheses hold:
 - 1 < p and mu(B_(t_1)) < infinity;
 - H is integrable on B_(t_1), by restriction;
 - the lower integral over B_(t_1) of |H|^p is finite, by step 2;
 - psi is continuous, so a.e.-strongly measurable, with 0 <= psi <= 1, and psi(x) = 0 when r_x > t_1 (step 1).
 It gives |E(t)| <= t_1 ((lower integral over B_(t_1) of |H|^p).toReal)^(1/p) I(t)^(1 - 1/p) <= 2 t N I(t)^(1 - 1/p), using step 2.

8. Bound on a and continuity: proof of (1). Let t > 0 with (1+eps) t < R, i.e. t in (0, R').
 - Put A := I(t)/t^n >= 0. Then I(t)^(1-1/p) = A^(1-1/p) t^(n - n/p).
 - A^(1-1/p) <= 1 + A: if A <= 1 the left side is <= 1, otherwise it is <= A.
 - Hence |a(t)| = |E(t)|/(t^(n+1)(1 + A)) <= 2 N t^(-n/p) A^(1-1/p)/(1 + A) <= 2 N t^(-n/p).
 - By step 2 this is <= 2 kappa Lambda R^(n/p - 1) t^(-n/p) = 2 kappa Lambda R^(-1) (t/R)^(-n/p) = b(t).
 - a = E/t^(n+1)/(1 + I/t^n) is continuous at t by 4(a) and 4(b), since t^(n+1) != 0 and 1 + I(t)/t^n >= 1.
 This is (1).

9. Integrating factor.
 - Apply integrating_factor on (0, R') with I, I', E, Q, a, M := 2 kappa Lambda R^(n/p - 1) and beta := n/p < 1. Indeed b(t) = M t^(-n/p).
 - Its hypotheses are 4(a), 4(b), 4(c), the sign I >= 0 from step 6, the identity of step 5, the definition of a, and step 8.
 - Hence for 0 < s <= r < R': Phi~(r) - Phi~(s) = integral_s^r exp(-G(t)) Q(t)/t^n dt.

10. Size of G. For 0 < t < R' (so t < R):
 - |G(t)| <= integral_0^t |a| <= integral_0^t b.
 - integral_0^t b = 2 kappa Lambda R^(-1) R^(n/p) t^(1-n/p)/(1 - n/p) = (2 kappa/alpha') Lambda (t/R)^(alpha') = (Lambda/2)(t/R)^(alpha') <= Lambda/2.
 - Hence exp(-G(t)) >= exp(-Lambda/2) > 0.

11. Monotonicity: first half of (2). Let 0 < s <= r with (1+eps) r < R, i.e. r < R'. On [s, r] the integrand exp(-G) Q/t^n is >= 0 by step 6. So, by step 9, Phi~(s) <= Phi~(r).

12. Annular estimate: second half of (2).
 - By steps 6 and 10, for t in [s, r]: Q(t)/t^n <= exp(Lambda/2) exp(-G(t)) Q(t)/t^n.
 - Integrating over [s, r] and using step 9: integral_s^r Q(t)/t^n dt <= exp(Lambda/2)(Phi~(r) - Phi~(s)).
 - Apply annular_tonelli with the same mu, w, y, phi, R, eps, s, r (its hypotheses are among ours). Its Q is the Q above.
 - By monotonicity of ofReal, the lower integral over closedBall y r minus ball y ((1+eps) s) of ofReal(w(x)/r_x^n) dmu is at most ofReal(integral_s^r Q(t)/t^n dt), which is at most ofReal(exp(Lambda/2)(Phi~(r) - Phi~(s))).
 This completes (2).

## Key steps

1. Constants: p > 1 and 2 kappa/(1 - n/p) = 1/2. Q_R < infinity and N := Q_R^(1/p) <= kappa Lambda R^(n/p - 1).
2. cutoff_calculus with T = 1 + eps and f = 1, (x - y).H, w: I is differentiable with derivative I', and E and Q are continuous on (0, R/(1+eps)).
3. The radial identity at rho = t, split by linearity, gives n I - t I' + t Q = -E; also I >= 0 and Q >= 0.
4. holder_bound at radius (1+eps)t <= 2t with psi = phi(r_x/t) gives |E(t)| <= 2tN I^(1-1/p). With A = I/t^n and A^(1-1/p) <= 1 + A, |a(t)| <= b(t) = 2 kappa Lambda R^(-1)(t/R)^(-n/p), and a is continuous.
5. integrating_factor with M = 2 kappa Lambda R^(n/p - 1) and beta = n/p gives Phi~(r) - Phi~(s) = integral_s^r exp(-G) Q/t^n.
6. |G(t)| <= integral_0^t b = (Lambda/2)(t/R)^(1-n/p) <= Lambda/2, so exp(-G) >= exp(-Lambda/2); Q >= 0 gives monotonicity.
7. integral_s^r Q/t^n <= exp(Lambda/2)(Phi~(r) - Phi~(s)), and annular_tonelli bounds the conical lower integral over closedBall y r minus ball y ((1+eps)s) by ofReal of the left side.

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
