# Parent-supplied natural-language proof

- Parent DAG node: `root.affine_approximation-a1.lp_monotonicity-a1.cutoff_squeeze-a1`
- Child DAG node: `root.affine_approximation-a1.lp_monotonicity-a1.cutoff_squeeze-a1.derivative_squeeze-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 7-10 of the parent proof, i.e. Simon Ch. 4, 3.4 -> 3.5 ('by integration in 3.4') with the corrected prefactors. We use the pointwise inequality of parent step 9,
 r^(-n) d_t phi(r/t) <= t^(-n) d_t phi(r/t) <= (1 + epsilon)^n r^(-n) d_t phi(r/t),
but integrate it first in x at fixed t and then in t. Integrating in this order compares derivatives directly and needs no exchange of integrals (Fubini). The sibling theorem cutoff_derivative is: for an a.e.-bounded, a.e. strongly measurable weight q with |q| <= B a.e., 0 < t and (1 + epsilon) t < S, the functions phi(r/t) q and (r/t) phi'(r/t) q are mu-integrable and s -> integral phi(r/s) q dmu has derivative -(1/t) integral (r/t) phi'(r/t) q dmu at t.

0. Admissible radii. For t in [sigma, rho], t >= sigma > 0 and (1 + epsilon) t <= (1 + epsilon) rho < S. So cutoff_derivative applies at every t in [sigma, rho].

1. Facts about phi.
 - phi'(s) = 0 for s < 1, because phi = 1 on the open neighbourhood (-infinity, 1) of s.
 - phi'(s) = 0 for s > 1 + epsilon, because phi = 0 on (1 + epsilon, infinity).
 - phi' <= 0 everywhere, because phi is nonincreasing and differentiable.

2. Comparison weight. Put q(x) := w(x)/max(sigma, r)^n.
 - q is mu-a.e. strongly measurable: w is a.e. strongly measurable, and x -> max(sigma, r)^n is continuous and positive since max(sigma, r) >= sigma > 0.
 - For mu-a.e. x we have 0 <= w(x) <= 1, so |q(x)| <= 1/max(sigma, r)^n <= 1/sigma^n.
 - Also |w| <= 1 mu-a.e.

3. Sibling facts. Let G(s) := integral phi(r/s) q dmu for real s. For t in [sigma, rho] put G'(t) := -(1/t) integral (r/t) phi'(r/t) q dmu.
 - cutoff_derivative with weight q and bound B = sigma^(-n), at every t in [sigma, rho]: x -> phi(r/t) q(x) and x -> (r/t) phi'(r/t) q(x) are mu-integrable, and G is differentiable at t with derivative G'(t).
 - cutoff_derivative with weight w and bound B = 1: x -> (r/t) phi'(r/t) w(x) is mu-integrable.

4. Pointwise squeeze. Fix t in [sigma, rho] and put D(x) := -(r/t) phi'(r/t)/t, the t-derivative of phi(r/t). Then D >= 0, since r/t >= 0, phi' <= 0 and t > 0. Claim: for mu-a.e. x (those with 0 <= w(x) <= 1),
 D q <= D w/t^n <= (1 + epsilon)^n D q, and D q >= 0.
 - If phi'(r/t) = 0, then D(x) = 0 and all quantities vanish.
 - Otherwise step 1 forces 1 <= r/t <= 1 + epsilon, i.e. t <= r <= (1 + epsilon) t. In particular r >= t >= sigma > 0, so max(sigma, r) = r and q(x) = w(x)/r^n. Moreover D w >= 0 and t^n <= r^n <= (1 + epsilon)^n t^n. Hence D w/r^n <= D w/t^n, D w/t^n <= (1 + epsilon)^n D w/r^n, and D w/r^n >= 0.

5. Integrated squeeze.
 - By linearity, G'(t) = integral D q dmu and J'(t)/t^n = integral D w/t^n dmu.
 - Both integrands are mu-integrable: they are constant multiples of the integrable functions of step 3.
 Integrating step 4 (monotonicity of the integral) gives, for every t in [sigma, rho],
 G'(t) <= J'(t)/t^n <= (1 + epsilon)^n G'(t) and G'(t) >= 0.

6. Derivative comparison. Let t be in [sigma, rho]. By step 5, J'(t)/t^n >= G'(t) >= 0. Together with e^(-c) <= F(t) <= e^c:
 Psi'(t) = F(t) J'(t)/t^n >= e^(-c) J'(t)/t^n >= e^(-c) G'(t),
 Psi'(t) = F(t) J'(t)/t^n <= e^c J'(t)/t^n <= e^c (1 + epsilon)^n G'(t).

7. Integration over [sigma, rho]. Let f_1 := Psi - e^(-c) G and f_2 := e^c (1 + epsilon)^n G - Psi.
 - Both are differentiable at every point of [sigma, rho] (step 3 and the hypothesis on Psi), with nonnegative derivatives there (step 6).
 - A function differentiable at every point of [sigma, rho] is continuous on [sigma, rho]. If its derivative is >= 0 on (sigma, rho), the mean value theorem shows it is nondecreasing on [sigma, rho].
 Thus f_i(sigma) <= f_i(rho) for i = 1, 2, i.e.
 e^(-c)(G(rho) - G(sigma)) <= Psi(rho) - Psi(sigma) <= e^c (1 + epsilon)^n (G(rho) - G(sigma)).

8. Identification of A. By step 3 at t = rho and t = sigma, phi(r/rho) q and phi(r/sigma) q are mu-integrable. So G(rho) - G(sigma) = integral (phi(r/rho) - phi(r/sigma)) q dmu. For every x, (phi(r/rho) - phi(r/sigma)) q(x) = (phi(r/rho) - phi(r/sigma)) w(x)/r^n:
 - if r <= sigma, then r/sigma <= 1 and r/rho <= 1 (as r <= sigma <= rho). So phi(r/rho) = phi(r/sigma) = 1 and both sides vanish; this case includes x = y;
 - if r > sigma, then max(sigma, r) = r and q(x) = w(x)/r^n.
 Hence G(rho) - G(sigma) = A, and step 7 is the assertion. QED

## Key steps

1. Every t in [sigma, rho] is admissible for cutoff_derivative; phi' = 0 outside [1, 1+epsilon], and phi' <= 0.
2. With the comparison weight q = w/max(sigma, r)^n, |q| <= sigma^(-n), G(t) = integral phi(r/t) q dmu has derivative G'(t) = -(1/t) integral (r/t) phi'(r/t) q dmu.
3. Where d_t phi(r/t) != 0 we have t <= r <= (1+epsilon)t and q = w/r^n, so D q <= D w/t^n <= (1+epsilon)^n D q. Integrating in x gives G' <= J'/t^n <= (1+epsilon)^n G' and G' >= 0.
4. With e^(-c) <= F <= e^c, e^(-c) G' <= Psi' <= e^c (1+epsilon)^n G' on [sigma, rho].
5. By the mean value theorem, e^(-c)(G(rho)-G(sigma)) <= Psi(rho)-Psi(sigma) <= e^c (1+epsilon)^n (G(rho)-G(sigma)).
6. G(rho) - G(sigma) = A, because phi(r/rho) - phi(r/sigma) = 0 for r <= sigma and q = w/r^n for r > sigma.

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
