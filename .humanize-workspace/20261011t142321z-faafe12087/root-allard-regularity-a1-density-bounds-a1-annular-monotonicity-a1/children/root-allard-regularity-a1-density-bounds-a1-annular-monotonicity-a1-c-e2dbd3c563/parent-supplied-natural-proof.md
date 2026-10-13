# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1`
- Child DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1, 5, 6, 7 and 8 of the parent proof: the cutoff construction, the passage eps -> 0 by dominated convergence, the bounds (i), monotonicity, and Fatou's lemma for the annular term (Simon, Ch. 4, 4.5-4.8). They are stated for an abstract measure mu and weight w. The proof uses the sibling lemma fixed_cutoff.

Notation:
- r_x := |x - y| and B_t := closedBall y t;
- kappa := (p - n)/(4p) and alpha' := 1 - n/p;
- b(t) := 2 kappa Lambda R^(-1) (t/R)^(-n/p) for t > 0;
- m(t) := mu(B_t).toReal.

1. Cutoffs.
 - Let psi(v) := 1 for v <= 0, psi(v) := 1 - 3v^2 + 2v^3 for 0 <= v <= 1, and psi(v) := 0 for v >= 1.
 - psi is C^1: psi'(v) = 6v(v - 1) on [0, 1], which vanishes at 0 and 1, and psi' = 0 outside [0, 1]. It is nonincreasing (psi' <= 0) with values in [0, 1].
 - For eps > 0 put phi_eps(u) := psi((u - 1)/eps). Then phi_eps is C^1 and nonincreasing, phi_eps = 1 on (-infinity, 1], and phi_eps = 0 on [1+eps, infinity).
 - Any family with these four properties may be used instead, e.g. u -> 1 - smoothTransition((u - 1)/eps).
 - For every u, phi_eps(u) -> 1_{u <= 1} as eps -> 0+: for u > 1, phi_eps(u) = 0 once eps <= u - 1.

2. A sequence of cutoffs. Let eps_k := 1/(k+2), so 0 < eps_k <= 1/2 and eps_k -> 0. Define
 - phi_k := phi_(eps_k);
 - I_k(t) := integral phi_k(r_x/t) dmu;
 - E_k(t) := integral phi_k(r_x/t)(x - y).H(x) dmu;
 - a_k(t) := E_k(t)/t^(n+1)/(1 + I_k(t)/t^n);
 - G_k(t) := integral_0^t a_k;
 - Phi~_k(t) := exp(-G_k(t))(1 + I_k(t)/t^n).

3. Fixed-cutoff facts. For each k apply fixed_cutoff with eps := eps_k (0 < eps_k <= 1), phi := phi_k, I := I_k, E := E_k and a := a_k. The defining equations hold by definition. The radial-identity hypothesis for phi_k is the assumed radial identity with T := 1 + eps_k. We obtain:
 (A_k) for t > 0 with (1+eps_k) t < R: a_k is continuous at t and |a_k(t)| <= b(t);
 (B_k) for 0 < s <= r with (1+eps_k) r < R: Phi~_k(s) <= Phi~_k(r), and the lower integral over A_k(s, r) of ofReal(w(x)/r_x^n) dmu is at most ofReal(exp(Lambda/2)(Phi~_k(r) - Phi~_k(s))). Here A_k(s, r) := closedBall y r minus ball y ((1+eps_k) s).

4. Limit objects.
 - E(t) := integral_{B_t} (x - y).H(x) dmu and a(t) := E(t)/t^(n+1)/(1 + m(t)/t^n);
 - G(t) := integral_0^t a, and F(t) := exp(-G(t)) for all real t;
 - Phi(t) := F(t)(t^n)^(-1) m(t) + F(t) - 1 = F(t)(1 + m(t)/t^n) - 1 for t > 0.

5. Pointwise convergence at a radius. Fix t in (0, R). Since eps_k -> 0, there is k_0 with (1+eps_k) t < R for k >= k_0. For such k:
 - 0 <= phi_k(r_x/t) <= 1_{B_R}(x), and |phi_k(r_x/t)(x - y).H(x)| <= R |H(x)| 1_{B_R}(x), since both vanish when r_x > (1+eps_k) t.
 - These bounds are integrable, because mu(B_R) < infinity and H is integrable on B_R.
 - The integrands are a.e.-strongly measurable: continuous functions times H, supported in B_R.
 For every x, phi_k(r_x/t) -> 1_{r_x/t <= 1} = 1_{B_t}(x) by step 1. By dominated convergence:
 - I_k(t) -> integral 1_{B_t} dmu = m(t);
 - E_k(t) -> integral 1_{B_t}(x)(x - y).H(x) dmu = E(t).
 As t^(n+1) > 0 and 1 + I_k(t)/t^n -> 1 + m(t)/t^n >= 1, we get a_k(t) -> a(t).

6. Convergence of G_k. Fix t in (0, R) and k_0 as in step 5. For k >= k_0 and tau in (0, t] we have (1+eps_k) tau < R, so by (A_k):
 - a_k is continuous on (0, t], hence a.e.-strongly measurable for Lebesgue measure on (0, t];
 - |a_k(tau)| <= b(tau).
 b is integrable on (0, t] because -n/p > -1. Explicitly, integral_0^t b = 2 kappa Lambda R^(-1) R^(n/p) t^(1-n/p)/(1-n/p) = (2 kappa/alpha') Lambda (t/R)^(alpha') = (Lambda/2)(t/R)^(alpha'), using 2 kappa/alpha' = 1/2.
 By step 5 at each tau in (0, t], a_k(tau) -> a(tau). By dominated convergence for interval integrals, G_k(t) -> G(t). Hence exp(-G_k(t)) -> F(t), and Phi~_k(t) -> F(t)(1 + m(t)/t^n) = Phi(t) + 1.

7. Conclusion (i). Let r be in (0, R).
 - For k >= k_0, |G_k(r)| <= integral_0^r |a_k| <= integral_0^r b = (Lambda/2)(r/R)^(alpha').
 - Letting k -> infinity, |G(r)| <= (Lambda/2)(r/R)^(alpha') <= Lambda/2 <= 1/2, since r < R and Lambda <= 1.
 - Hence exp(-Lambda) <= exp(-Lambda/2) <= F(r) = exp(-G(r)) <= exp(Lambda/2) <= exp(Lambda).
 - By |exp(z) - 1| <= 2|z| for |z| <= 1, |F(r) - 1| <= 2|G(r)| <= Lambda (r/R)^(alpha').

8. Conclusion (ii), monotonicity. Let 0 < s <= r < R.
 - For k large, (1+eps_k) r < R, and (B_k) gives Phi~_k(s) <= Phi~_k(r).
 - Letting k -> infinity (step 6 at s and at r), Phi(s) + 1 <= Phi(r) + 1, i.e. Phi(s) <= Phi(r).
 - Written out: F(s)(s^n)^(-1) m(s) + F(s) - 1 <= F(r)(r^n)^(-1) m(r) + F(r) - 1.

9. Conclusion (ii), annular bound. Let 0 < s <= r < R and g(x) := ofReal(w(x)/r_x^n).
 (a) Convergence of the indicators.
  - A_k(s, r) is contained in B_r minus B_s for every k: x in A_k gives r_x >= (1+eps_k) s > s and r_x <= r.
  - Every x in B_r minus B_s lies in A_k(s, r) for all large k, because r_x > s and (1+eps_k) s -> s.
  - Hence 1_{A_k(s,r)}(x) g(x) -> 1_{B_r minus B_s}(x) g(x) for every x, so liminf_k 1_{A_k} g = 1_{B_r minus B_s} g.
 (b) Measurability. Each 1_{A_k} g is a.e.-measurable for mu: A_k lies in B_r, which lies in ball y R, and g is a.e.-measurable for mu restricted to ball y R, because w is a.e.-strongly measurable there.
 (c) Fatou's lemma, then (B_k) for k large, then step 6 with the continuity of ofReal:
  lower integral over B_r minus B_s of g dmu
  = lower integral of liminf_k 1_{A_k} g dmu
  <= liminf_k (lower integral over A_k of g dmu)
  <= liminf_k ofReal(exp(Lambda/2)(Phi~_k(r) - Phi~_k(s)))
  = ofReal(exp(Lambda/2)(Phi(r) - Phi(s))).
 (d) Phi(r) - Phi(s) >= 0 by step 8, and exp(Lambda/2) <= exp(Lambda). So the right side is at most ofReal(exp(Lambda)(Phi(r) - Phi(s))).
 This is the annular bound of (ii) for the F of step 4.

## Key steps

1. There are C^1 nonincreasing cutoffs phi_eps (cubic profile) equal to 1 on (-infinity, 1] and 0 on [1+eps, infinity), with phi_eps -> 1_{u <= 1}.
2. fixed_cutoff for eps_k = 1/(k+2) gives |a_k| <= b, continuity of a_k, monotonicity of Phi~_k and the per-k annular estimate.
3. Dominated convergence at each t in (0, R): I_k(t) -> m(t), E_k(t) -> E(t), and hence a_k(t) -> a(t).
4. Dominated convergence on (0, t] with bound b: G_k(t) -> G(t). Set F := exp(-G); then Phi~_k -> Phi + 1.
5. |G(t)| <= (Lambda/2)(t/R)^(1-n/p) <= 1/2 gives (i), via |e^z - 1| <= 2|z|.
6. Monotonicity of Phi~_k passes to the limit.
7. Fatou's lemma for the indicators of A_k = closedBall y r minus ball y ((1+eps_k)s), which converge to B_r minus B_s, gives the annular bound with exp(Lambda/2) <= exp(Lambda).

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
