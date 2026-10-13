# Parent-supplied natural-language proof

- Parent DAG node: `root.affine_approximation-a1.pinched_density_bounds-a1`
- Child DAG node: `root.affine_approximation-a1.pinched_density_bounds-a1.allard_subball_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the items (K-mono) and (A) of the notation section of the parent proof, and the facts derived from them in step 3 of the parent proof (B_S(y) in U, finiteness of the |H|^p integral over B_S(y), K(y,R) <= delta, mu(B_R(y)) <= (1 + delta) omega_n rho^n), stated for a general sub-ball B_r(z) of B_rho(0).

Notation: mu := V.weight, B_s(w) := closedBall w s, I(w,s) := integral^-_{B_s(w)} ||H(x)||_e^p dmu(x) in [0,infinity], and K(w,s) := V.scaledLpNorm H p w s = (ofReal(s^(p-n)) * I(w,s))^(1/p) in [0,infinity].

1. By definition, V.AllardHypotheses H p delta rho contains: rho > 0, B_rho(0) contained in U, mu(B_rho(0)) <= ofReal((1 + delta)(omega_n rho^n)), and K(0,rho) <= ofReal(delta). (Its remaining components - generalized mean curvature, theta >= 1 mu-a.e., 0 in spt V - are not needed here.) Since n >= 0 and p > n we have p > 0, 1/p > 0 and p - n > 0.

2. (a) B_r(z) is contained in B_rho(0), which is contained in U.

3. (d) By monotonicity of the measure mu, mu(B_r(z)) <= mu(B_rho(0)) <= ofReal((1 + delta)(omega_n rho^n)).

4. Since B_r(z) is contained in B_rho(0) and the integrand is nonnegative, monotonicity of the lower Lebesgue integral in the domain gives I(z,r) <= I(0,rho).

5. (c) (K-mono) Since 0 < r <= rho and p - n >= 0, r^(p-n) <= rho^(p-n), hence ofReal(r^(p-n)) <= ofReal(rho^(p-n)). Together with step 4 and monotonicity of multiplication in [0,infinity], ofReal(r^(p-n)) I(z,r) <= ofReal(rho^(p-n)) I(0,rho). Since 1/p >= 0, the map x -> x^(1/p) is monotone on [0,infinity], so K(z,r) <= K(0,rho) <= ofReal(delta).

6. (b) We have K(0,rho) <= ofReal(delta) < infinity. If ofReal(rho^(p-n)) I(0,rho) were infinite, then K(0,rho) = infinity^(1/p) = infinity because 1/p > 0, a contradiction; so ofReal(rho^(p-n)) I(0,rho) < infinity. As rho > 0, rho^(p-n) > 0, so ofReal(rho^(p-n)) is nonzero; a product in [0,infinity] whose first factor is nonzero and whose second factor is infinite is infinite, hence I(0,rho) < infinity. By step 4, I(z,r) <= I(0,rho) < infinity, which is (b).

## Key steps

1. Unpack rho > 0, B_rho(0) in U, the mass bound and K(0,rho) <= delta from AllardHypotheses; p > n >= 0 gives p > 0.
2. Ball inclusion gives (a) directly and (d) by monotonicity of mu.
3. r^(p-n) <= rho^(p-n), domain monotonicity of the lower integral and monotonicity of x^(1/p) give K(z,r) <= K(0,rho) <= delta.
4. K(0,rho) < infinity and rho^(p-n) > 0 force integral^-_{B_rho(0)} |H|^p < infinity, hence the integral over B_r(z) is finite.

## Reference use

### local-project

Queries:
- `timeout 300 rg -n "aal_|pinched|scaledLpNorm_mono|scaledLpNorm_le" <snapshot>/project`
- `timeout 300 rg -n "theorem lintegral_iUnion_le|theorem lintegral_union |theorem lintegral_union_le|theorem ofReal_integral_eq_lintegral_ofReal|theorem lintegral_singleton|theorem lintegral_biUnion_finset|theorem lintegral_mono_set " <snapshot>/mathlib/Mathlib`
- `timeout 300 rg -n "theorem add_one_le_exp|theorem one_add_mul_self_le_rpow_one_add|theorem continuousAt_rpow_const|theorem rpow_le_rpow |theorem rpow_le_one |theorem Gamma_pos_of_pos|theorem ofReal_le_iff_le_toReal" <snapshot>/mathlib/Mathlib`
- `timeout 300 rg -n "lemma one_add_mul_le_pow|theorem toReal_le_of_le_ofReal|theorem top_rpow_of_pos|theorem lt_top_of_mul_ne_top_right|theorem closedBall_subset_closedBall'|lemma div_le_iff₀|lemma le_div_iff₀|lemma integral_nonneg" <snapshot>/mathlib/Mathlib`
- `timeout 300 rg -n "restrict_iUnion_eq_iSup|lintegral_iUnion_mono|restrict_iUnion_apply_eq_iSup|lintegral_iSup_restrict" <snapshot>/mathlib/Mathlib; grep theorem/lemma in MeasureTheory/Measure/Continuity.lean; rg -n "theorem withDensity_apply " MeasureTheory/Measure/WithDensity.lean`
- `timeout 300 rg -n "Ioo_mem_nhdsGT|theorem exp_le_one_iff|theorem exp_le_exp|theorem exp_nat_mul" <snapshot>/mathlib/Mathlib`
- `python3 -I dag.json lean_name listing (collision check for aal_pinched_constants, aal_allard_subball_bounds, aal_monotone_quantity_ge_density, aal_lintegral_closedBall_le_of_annuli)`
- `python3 -I: verifier/lean_contract.validate_lean_statement + verifier/gmt-compare.child_modules(mode=contract) on the 4 child lean_statements`
- `lean -R /tmp/pdb/proj -o .../GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean (frozen Submission, pinned toolchain, LEAN_PATH = lake-packages-25730c7c builds)`
- `lean /tmp/pdb/proj/Combined.lean (4 child proofs + sorry-free parent assembly from children and verbatim sibling stubs; #print axioms)`
- `lean NodeChallenge.lean / NodeSolution.lean per child against a scratch Submission containing the child proofs`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Complex/Exponential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Order/Ring/Pow.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-pinched-density-bounds-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/pdb/proj/Combined.lean`

Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json).

No reuse is possible:
- The snapshot project has no match for aal_, pinched or scaledLpNorm-monotonicity; it contains only the frozen contract.
- None of the four proposed names occurs in dag.json.

Mathlib items located in the snapshot and used in the scratch Lean proofs (paths under mathlib/Mathlib):
- MeasureTheory/Integral/Lebesgue/Basic.lean: lintegral_mono_set (:98), lintegral_iUnion_le (:623), lintegral_union (:628).
- Lebesgue/Countable.lean: lintegral_singleton (:131).
- Bochner/Basic.lean: integral_nonneg (:649), ofReal_integral_eq_lintegral_ofReal (:739).
- Measure/WithDensity.lean: withDensity_apply (:44), valid for any integrand on measurable sets.
- Measure/Continuity.lean: Monotone.measure_iUnion (:71). There is no lintegral-over-monotone-union lemma, hence the withDensity route.
- Analysis/Complex/Exponential.lean: add_one_le_exp (:632), exp_le_exp (:316), exp_le_one_iff (:339), exp_nat_mul (:233).
- Algebra/Order/Ring/Pow.lean: Bernoulli one_add_mul_le_pow (:99).
- Pow/Real.lean: rpow_le_rpow (:549), rpow_le_one (:661).
- Pow/Continuity.lean: continuousAt_rpow_const (:220).
- Pow/NNReal.lean: ENNReal.rpow_le_rpow (:798), top_rpow_of_pos (:508).
- Gamma/Basic.lean: Gamma_pos_of_pos (:443).
- Basic/ENNReal/Real.lean: ofReal_le_iff_le_toReal (:262), toReal_le_of_le_ofReal (:283).
- Basic/ENNReal/Operations.lean: lt_top_of_mul_ne_top_right (:208).
- Topology/MetricSpace/Pseudo/Defs.lean: closedBall_subset_closedBall' (:547).
- Algebra/Order/GroupWithZero/Basic.lean: le_div_iff₀ (:1128), div_le_iff₀ (:1132).
- Ioo_mem_nhdsGT is available.

Lean checks:
- All 4 child types pass validate_lean_statement and elaborate in the comparator's contract scope (open MeasureTheory Metric Set Filter Topology; open scoped ENNReal NNReal; namespace GMT.Ch05; open RectifiableVarifold).
- Each child's NodeSolution (exact Submission.X) compiles.
- Combined.lean proves all 4 children with axioms propext, Classical.choice, Quot.sound only, and assembles the exact frozen parent type sorry-free from them plus verbatim stubs of aal_lp_monotonicity and aal_density_ge_one.
