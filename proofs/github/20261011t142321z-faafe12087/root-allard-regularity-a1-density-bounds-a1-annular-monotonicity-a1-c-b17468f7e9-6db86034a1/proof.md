# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_calculus-a1`
- Child DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.cutoff_calculus-a1.cutoff_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1-5 and 7 of the parent proof (part (c)).

Notation: r_x := |x - y|, phi' := deriv phi, B_S := closedBall y S, nu := mu restricted to B_S. Since f is mu-integrable on B_S, f is nu-integrable. Put
 F(s, x) := phi(r_x/s) f(x)   and   F'(s, x) := -s^(-1) (r_x/s) phi'(r_x/s) f(x).

1. Neighbourhood.
 - Since T > 0 and T t < S, we have t < R := S/T.
 - Let N := (t/2, R). It is an open interval containing t and contained in (0, infinity), and T s < S for every s in N.
 - The parent's interval (t/2, t_1), with t_1 = (t + S/T)/2, is a subinterval of N. Either works.

2. Vanishing.
 - phi = 0 on [T, infinity). If u > T, then phi vanishes on the open neighbourhood (T, infinity) of u, so phi'(u) = 0. Thus phi' = 0 on (T, infinity).
 - Let 0 < s < R and let x lie outside B_S, so r_x > S. Then r_x/s > S/s > T. Hence phi(r_x/s) = 0 and phi'(r_x/s) = 0.
 - So, for 0 < s < R, x -> F(s, x) vanishes outside B_S. Since B_S is closed, hence measurable, integral F(s, x) dmu(x) = integral F(s, x) dnu(x).
 - Likewise x -> (r_x/t) phi'(r_x/t) f(x) vanishes outside B_S (take s = t, which lies in (0, R)). So its mu- and nu-integrals agree.

3. Bounds.
 - phi and phi' are continuous, since phi is C^1. Let C_0 := max over [0, T] of |phi| and C_1 := max over [0, T] of |u phi'(u)|. Both are finite, because [0, T] is a nonempty compact interval, and both are >= 0.
 - For u >= 0 we have |phi(u)| <= C_0 and |u phi'(u)| <= C_1. On [0, T] this is the definition; for u > T both functions vanish (step 2).
 - Since r_x/s >= 0 for s > 0, |F(t, x)| <= C_0 |f(x)| for every x.
 - For s in N and every x: |F'(s, x)| = s^(-1) |(r_x/s) phi'(r_x/s)| |f(x)| <= (C_1/s) |f(x)| <= (2 C_1/t) |f(x)|, because s > t/2 > 0.
 - C_0 |f| and (2 C_1/t) |f| are nu-integrable, because f is.

4. Measurability and integrability.
 - f is a.e.-strongly measurable for nu.
 - For each fixed s > 0, x -> phi(r_x/s) and x -> -s^(-1)(r_x/s) phi'(r_x/s) are continuous, because phi and phi' are continuous. Hence F(s, .) and F'(s, .) are a.e.-strongly measurable for nu.
 - By step 3, |F(t, .)| <= C_0 |f|, so F(t, .) is nu-integrable.

5. Pointwise derivative.
 - Fix x and s different from 0. The map u -> r_x/u has derivative -r_x/s^2 at s.
 - phi is differentiable. By the chain rule, u -> phi(r_x/u) has derivative phi'(r_x/s)(-r_x/s^2) = -s^(-1)(r_x/s) phi'(r_x/s) at s.
 - Multiplying by the constant f(x): u -> F(u, x) has derivative F'(s, x) at s. In particular this holds for every s in N.

6. Differentiation under the integral sign. Apply it for the measure nu on the neighbourhood N of t:
 - F(s, .) is a.e.-strongly measurable for nu for every s in N (step 4);
 - F(t, .) is nu-integrable (step 4);
 - F'(t, .) is a.e.-strongly measurable for nu (step 4);
 - for every x and every s in N, |F'(s, x)| <= (2 C_1/t) |f(x)|, a nu-integrable function (step 3);
 - for every x and every s in N, u -> F(u, x) has derivative F'(s, x) at s (step 5).
 Hence s -> integral F(s, x) dnu(x) has derivative integral F'(t, x) dnu(x) at t.

7. Evaluation and transfer to mu.
 - By linearity of the integral and step 2 at s = t:
   integral F'(t, x) dnu = -(integral (r_x/t) phi'(r_x/t) f(x) dnu)/t = -(integral (r_x/t) phi'(r_x/t) f(x) dmu)/t.
 - By step 2, s -> integral F(s, x) dmu and s -> integral F(s, x) dnu agree on (0, R), a neighbourhood of t. A derivative at t depends only on the values of the function near t.
 - Therefore s -> integral phi(r_x/s) f(x) dmu has derivative -(integral (r_x/t) phi'(r_x/t) f(x) dmu)/t at t.

## Key steps

1. Since T t < S, t < R := S/T. Work on N = (t/2, R), which lies in (0, infinity).
2. phi' = 0 on (T, infinity). For 0 < s < R the integrands vanish outside B_S(y), so mu-integrals equal integrals against nu = mu restricted to B_S(y).
3. |phi| <= C_0 and |u phi'(u)| <= C_1 on [0, infinity). Hence |F(t,.)| <= C_0|f|, and for s in N, |F'(s,.)| <= (2 C_1/t)|f|.
4. F(s,.) and F'(s,.) are continuous functions of x times f, hence a.e.-strongly measurable for nu; F(t,.) is nu-integrable.
5. Chain rule: d/ds phi(r_x/s) = -s^(-1)(r_x/s) phi'(r_x/s).
6. Differentiation under the integral sign for nu on N gives the derivative integral F'(t,x) dnu at t.
7. Linearity evaluates this as -(integral (r_x/t) phi'(r_x/t) f dmu)/t. Agreement of the mu- and nu-integrals near t transfers the derivative.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean; cmp GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Submission.lean`
- `rg -n 'allard52_am_cc_|allard52_am_cutoff_integral_calculus' <snapshot>/project (exit 1, no match); rg -l 'allard52_am_cc_' <snapshot>/mathlib/Mathlib (exit 1, no match)`
- `python3 -I over dag.json: all 363 lean_name values (unique; neither new name present); lean_statement search for 'ContinuousAt (fun', 'HasDerivAt (fun', 'deriv φ', 'ContDiff ℝ 1 φ' and '‖x - y‖ / s'`
- `git show 723d4c5ace5b42523b4f5ae029e99054eba4c211 (accepted aal_cfs_hasDerivAt_cutoff_integral); git show 2627b345844aca5f755b25ea3df419f11a6bb507 (accepted aal_cfs_cutoff_pairing_continuousAt); sed GMT/Scratch/aal_mrc/aal_mrc_cutoff_integral_continuousOn.lean.txt`
- `rg -n over snapshot Mathlib: '^theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le', '^theorem continuousAt_of_dominated', '^theorem setIntegral_eq_integral_of_forall_compl_eq_zero', 'exists_bound_of_continuousOn', 'theorem ContDiff.continuous_deriv_one', 'theorem ContDiff.continuous', 'theorem Filter.EventuallyEq.deriv_eq', 'theorem HasDerivAt.congr_of_eventuallyEq', 'theorem hasDerivAt_inv', 'theorem ContinuousAt.congr', '^theorem integral_neg', '^theorem integral_div', '^theorem Integrable.mono', 'theorem Ioo_mem_nhds', 'theorem lt_mem_nhds'`
- `toolchains/lean-4.35.0-rc3-linux/bin/lean GMT/Ch05/Submission.lean -o /tmp/cc-decomp-tyO9i2/build/lib/GMT/Ch05/Submission.olean (LEAN_PATH = that build dir plus lake-packages-25730c7c/*/.lake/build/lib/lean)`
- `LEAN_PATH=<same> lean /tmp/cc-decomp-tyO9i2/check/Types.lean; Children.lean; SplitAll.lean; AssemblyAx.lean`
- `lean the candidate Submission_with_split as GMT.Ch05.Submission into build2; child_modules from verifier/gmt-compare.py (contract mode) for both children and the parent; NodeChallenge against the contract build; NodeSolution plus #print axioms against build2`
- `python3 -I leaf_gate_replay.py with /runtime/flows/gmt-claude-0135a42af877/_recursive_lean/leaf_verification.py and /runtime/flows/gmt-claude-0399b23aef86/_recursive_lean/leaf_verification.py`
- `validate_lean_statement (verifier/lean_contract.py) on the two child types and the parent type`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Continuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1-c-29d4916de4/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1-c-29d4916de4/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-lp-monotonicity-a1-cutoff-squeeze-a1-cut-94d5e39948/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-lp-monotonicity-a1-cutoff-squeeze-a1-pai-88745b4bc7/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/aal_mrc/aal_mrc_cutoff_integral_continuousOn.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/allard52_am_cc/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/allard52_am_cc/allard52_am_cc_split_all.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/allard52_am_cc/Submission_with_split.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/allard52_am_cc/assembly_from_child_axioms.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-0135a42af877/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-0399b23aef86/_recursive_lean/leaf_verification.py`

Pins. Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Submission.lean is byte-identical to Contract.lean and to the snapshot copy.

Names. No snapshot project or Mathlib file mentions allard52_am_cc_* or allard52_am_cutoff_integral_calculus (rg exit 1). dag.json has 363 nodes with unique lean_names, and neither new name is reserved.

Reuse. No snapshot or DAG declaration states either child. The closest accepted nodes have stronger hypotheses and different integrands, so neither can be reused:
- aal_cfs_cutoff_pairing_continuousAt: inner-product weight, antitone plateau cutoff;
- aal_cfs_hasDerivAt_cutoff_integral: bounded weight q, mu(B_S) < infinity, antitone plateau cutoff.
Their proofs, and the scratch aal_mrc_cutoff_integral_continuousOn, served as templates.

Mathlib tools, by location in the snapshot:
- ParametricIntegral.lean:286 hasDerivAt_integral_of_dominated_loc_of_deriv_le
- Bochner/Basic.lean:458 continuousAt_of_dominated; :256 integral_neg; :297 integral_div
- Bochner/Set.lean:486 setIntegral_eq_integral_of_forall_compl_eq_zero
- Normed/Group/Bounded.lean:91 IsCompact.exists_bound_of_continuousOn (generated by to_additive)
- ContDiff/Deriv.lean:113 ContDiff.continuous_deriv_one; ContDiff/Defs.lean:1150 ContDiff.continuous
- Deriv/Basic.lean:606 HasDerivAt.congr_of_eventuallyEq; :638 Filter.EventuallyEq.deriv_eq
- Deriv/Inv.lean:55 hasDerivAt_inv
- Topology/Continuous.lean:70 ContinuousAt.congr
- L1Space/Integrable.lean:104 Integrable.mono'
- OrderClosed.lean:611 Ioo_mem_nhds; Order/Basic.lean:124 lt_mem_nhds

Lean checks.
- Both child types and the parent type elaborate in the comparator's contract scope and pass validate_lean_statement.
- Complete proofs of both children and the parent assembly compile. Axioms: [propext, Classical.choice, Quot.sound].
- With the children as axioms, the parent depends on exactly those two axioms.
- Comparator-generated NodeChallenge/NodeSolution modules pass for all three.
- Both leaf-gate variants accept each insertion.

Evidence: GMT/Scratch/allard52_am_cc/ (git-ignored, SHA256SUMS).
