# Parent-supplied natural-language proof

- Parent DAG node: `root.affine_approximation-a1.lp_monotonicity-a1.cutoff_squeeze-a1`
- Child DAG node: `root.affine_approximation-a1.lp_monotonicity-a1.cutoff_squeeze-a1.cutoff_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof (Simon Ch. 4, 3.4: differentiability of I and J), for a general bounded weight q.

Notation:
- K := B_S(y), the closed ball.
- nu := mu restricted to K. Since nu(whole space) = mu(K) < infinity, nu is a finite measure.
- R* := S/(1 + epsilon). Since 1 + epsilon > 0 and (1 + epsilon) t < S, we have t < R*.
- U := (t/2, R*), an open interval containing t and contained in (0, R*).

1. Facts about phi.
 (a) 0 <= phi <= 1. For every s, s <= max(s, 1 + epsilon), so phi(s) >= phi(max(s, 1 + epsilon)) = 0. Also min(s, 1) <= s, so phi(s) <= phi(min(s, 1)) = 1.
 (b) phi and phi' are continuous, because phi is C^1.
 (c) phi'(s) = 0 for every s > 1 + epsilon, because phi vanishes on the open neighbourhood (1 + epsilon, infinity) of s.
 (d) There is C >= 0 with |u phi'(u)| <= C for all u >= 0. The continuous function u -> u phi'(u) is bounded on the compact interval [0, 1 + epsilon], say by C_0. For u > 1 + epsilon it vanishes by (c). Take C := max(C_0, 0).

2. Derivative in the scale. Let r be real and s != 0. Since d/du (r/u) = -r/u^2, the chain rule shows that u -> phi(r/u) is differentiable at u = s with derivative phi'(r/s)(-r/s^2) = -(r/s) phi'(r/s)/s.

3. Support. Let s be in (0, R*) and x not in K. Then r > S > (1 + epsilon) s, so r/s > 1 + epsilon. Hence phi(r/s) = 0, and phi'(r/s) = 0 by 1(c). So for every s in (0, R*):
 - x -> phi(r/s) q(x) and x -> (r/s) phi'(r/s) q(x) vanish outside K;
 - their mu-integrals equal their nu-integrals.

4. Integrability.
 - Fix any s. The function x -> phi(r/s) q(x) is nu-a.e. strongly measurable (a continuous function of x times q). By 1(a) it is bounded nu-a.e. by B. Since nu is finite, it is nu-integrable.
 - The function x -> (r/t) phi'(r/t) q(x) is nu-a.e. strongly measurable. By 1(d) with u = r/t >= 0 it is bounded nu-a.e. by C B, so it is nu-integrable.
 - By step 3 with s = t, both functions at scale t vanish outside K. A function that is integrable on K and vanishes outside K is mu-integrable.
 This proves the two integrability claims.

5. Differentiation under the integral sign for nu. Put F(s, x) := phi(r/s) q(x) and F'(s, x) := -(r/s) phi'(r/s) q(x)/s. We check the hypotheses of the theorem on differentiating a parametric integral with a locally uniform integrable dominating function (Mathlib: hasDerivAt_integral_of_dominated_loc_of_deriv_le), on the neighbourhood U of t.
 - For every s, F(s, .) is nu-a.e. strongly measurable, and F(t, .) is nu-integrable (step 4).
 - F'(t, .) is nu-a.e. strongly measurable (a continuous function of x times q).
 - Domination. Take any x with |q(x)| <= B; these are nu-almost all x, and for them B >= 0. Let s be in U. Then s > t/2 > 0, so by 1(d), |F'(s, x)| = |(r/s) phi'(r/s)| |q(x)|/s <= C B/s <= 2 C B/t. The constant 2 C B/t is nu-integrable because nu is finite.
 - For every x and every s in U, F(., x) is differentiable at s with derivative F'(s, x) (step 2, times the constant q(x)).
 Hence s -> integral F(s, x) dnu(x) is differentiable at t. By linearity its derivative is integral F'(t, x) dnu(x) = -(1/t) integral (r/t) phi'(r/t) q dnu.

6. Back to mu.
 - By step 3, integral phi(r/s) q dmu = integral phi(r/s) q dnu for every s in the neighbourhood (0, R*) of t. So the two functions of s coincide near t and have the same derivative at t.
 - Also by step 3, integral (r/t) phi'(r/t) q dnu = integral (r/t) phi'(r/t) q dmu.
 Therefore s -> integral phi(r/s) q dmu is differentiable at t with derivative -(1/t) integral (r/t) phi'(r/t) q dmu. QED

## Key steps

1. 0 <= phi <= 1, phi' is continuous, phi' = 0 on (1+epsilon, infinity), and |u phi'(u)| <= C for u >= 0.
2. For s != 0, d/ds phi(r/s) = -(r/s) phi'(r/s)/s.
3. For 0 < s < S/(1+epsilon) the integrands vanish outside B_S(y), so mu-integrals equal integrals for the finite measure nu = mu restricted to B_S(y).
4. Bounds B and C B on the finite measure nu give integrability, which transfers to mu.
5. On (t/2, S/(1+epsilon)) the s-derivatives are dominated by 2CB/t, so the nu-integral can be differentiated under the integral sign.
6. The nu- and mu-integrals agree near t, so the derivative at t is -(1/t) integral (r/t) phi'(r/t) q dmu.

## Reference use

### local-project

Queries:
- `timeout 300 rg -n "aal_cfs_|aal_cutoff_integrating_factor_squeeze|hasDerivAt_cutoff_integral|integrating_factor_deriv|squeeze_of_deriv" <snapshot>/project  (exit 1: no match)`
- `diff <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; diff <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean  (both identical)`
- `timeout 600 rg -n "^theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le|^theorem continuousAt_of_dominated|^theorem integral_hasDerivAt_right|^theorem intervalIntegrable_rpow'|^theorem monotoneOn_of_deriv_nonneg|^theorem setIntegral_eq_integral_of_forall_compl_eq_zero|^theorem integrableOn_iff_integrable_of_support_subset|^theorem div₀|^lemma Antitone.deriv_nonpos|^theorem abs_integral_le_integral_abs|^theorem integral_mono_interval|^theorem mono_fun'|^theorem ContDiff.continuous_deriv_one|^lemma Integrable.of_bound" <snapshot>/mathlib/Mathlib`
- `timeout 300 rg -n "integral_mono_ae\b|integral_nonneg_of_ae\b" <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `grep -n "^theorem|^def|^private theorem" .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/{FirstVariation,LpCancellation}.lean`
- `sed -n 215,560p book/chapter-04.txt (Simon Ch. 4, 3.1-3.17 and 4.1-4.8)`
- `python3 -I: dag.json lean_name collision check; git for-each-ref (607 refs) + git grep -l -e aal_cfs_ -- '*.lean' (no hits)`
- `python3 -I: verifier/lean_contract.py validate_lean_statement on the four child types`
- `lake env lean /tmp/claude-cfs/src/{Stmts,Assembly,All,AllHB}.lean against the contract olean (statements; sorry-free parent assembly; full proofs with #print axioms; #count_heartbeats)`
- `lake env lean --root=/tmp/claude-cfs/root -o .../GMT/Ch05/Submission.olean (contract + all five declarations) and gmt-compare.py child_modules NodeChallenge/NodeSolution compilation for all five types`
- `python3 -I leafcheck.py (harness check_source_delta replay for each single-theorem insertion)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpCancellation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_lmono/dohr_lmono_fixed_cutoff_monotone.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/aal_cfs/aal_cfs_split_all.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/aal_cfs/README.md`

Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The installed Mathlib has the same revision. The snapshot Contract and Submission are byte-identical to the workspace Contract.

The snapshot project has no declaration for this node or its proposed children (rg exit 1), so no project declaration is reused.

Every Mathlib result the child proofs use exists at the pinned revision (paths under mathlib/Mathlib):
- hasDerivAt_integral_of_dominated_loc_of_deriv_le (Analysis/Calculus/ParametricIntegral.lean:286);
- continuousAt_of_dominated (MeasureTheory/Integral/Bochner/Basic.lean:458);
- integral_mono_ae and integral_nonneg_of_ae (Bochner/Basic.lean:664, 644);
- setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:486);
- integrableOn_iff_integrable_of_support_subset (Integral/IntegrableOn.lean:462) and Integrable.of_bound (:171);
- intervalIntegral.integral_hasDerivAt_right (IntervalIntegral/FundThmCalculus.lean:725);
- IntervalIntegrable.mono_fun', abs_integral_le_integral_abs and integral_mono_interval (IntervalIntegral/Basic.lean:291, 1393, 1405);
- intervalIntegrable_rpow' (SpecialFunctions/Integrability/Basic.lean:47);
- monotoneOn_of_deriv_nonneg (Calculus/Deriv/MeanValue.lean:411);
- Antitone.deriv_nonpos (Deriv/Slope.lean:214);
- ContDiff.continuous_deriv_one (ContDiff/Deriv.lean:113);
- AEStronglyMeasurable.div₀ (StronglyMeasurable/AEStronglyMeasurable.lean:332).

Patterns adapted, not reused as declarations:
- SimonGMT Chapter04 hasDerivAt_integral_scaledRadialCutoff_mul (FirstVariation.lean:680) and HasGeneralizedMeanCurvatureIn.cancelledCutoffMass_squeeze (LpCancellation.lean:400). The latter integrates a derivative comparison with a truncated weight, the route child 4 follows. Both are stated for SimonGMT's own varifold structure, so they do not apply here.
- The kernel-checked scratch proof GMT/Scratch/dohr_lmono/dohr_lmono_fixed_cutoff_monotone.lean.txt, an inequality version of children 1-3.

The printed Simon Ch. 4, 3.4-3.5 and 4.3-4.4 (book/chapter-04.txt) matches the argument. Its prefactors in 3.5 are reversed and are used here in corrected form.

I wrote complete sorry-free Lean proofs of all four children and of the frozen parent type assembled from them (GMT/Scratch/aal_cfs). They use only propext, Classical.choice and Quot.sound. Every piece is a single theorem accepted by check_source_delta. gmt-compare.py challenge and solution modules compile for all five types. The proposed names are unreserved in dag.json and absent from all 607 git refs.
