# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.allard_density_bounds-a1`
- Child DAG node: `root.tilt_excess_decay-a1.allard_density_bounds-a1.support_diff_carrier_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 7 of the parent proof (Simon Ch. 3, Remark 1.8(2), via the Upper Density Theorem, Simon Ch. 1, 3.6), stated for an arbitrary open set W instead of the open ball B°_rho(0), and an arbitrary positive constant c instead of 1/2. The parent applies it with:
- W = B°_rho(0), where mu(W) <= mu(B_rho(0)) <= ofReal((1 + delta) omega_n rho^n) < infinity by AllardHypotheses;
- c = 1 - 1/2, supplied at each y in spt V ∩ B°_rho(0) by ted_density_ge_one with epsilon = 1/2.

Notation: mu := V.weight, the measure H^n restricted to M with density ofReal(theta), where M := V.carrier and theta := V.mult. H^n := μHE[n], omega_n := unitBallVolume n, and B_r(x) is the closed ball. Quotients are taken in [0, infinity].

1. omega_n > 0, because pi^(n/2) > 0 and Gamma(n/2 + 1) > 0 (as n/2 + 1 > 0). Hence omega_n r^n > 0 for every r > 0.

2. A Borel kernel of M. The carrier M is H^n-null-measurable (contract field nullMeasurableSet_carrier). By NullMeasurableSet.exists_measurable_subset_ae_eq there is a measurable set B ⊆ M with B = M H^n-almost everywhere. In particular H^n(M \ B) = 0.

3. mu(R^(n+l) \ B) = 0. The complement B^c is measurable, so by the definition of mu as a measure with density (withDensity_apply), mu(B^c) is the lower integral of ofReal(theta) over B^c with respect to H^n restricted to M. That restricted measure gives B^c the mass H^n(B^c ∩ M) = H^n(M \ B) = 0, and a lower integral over a null set vanishes. Consequently mu(T ∩ B) = mu(T) for every set T (measure_inter_conull).

4. The Upper Density Theorem. Put A := B ∩ W. It is measurable, since B is measurable and W is open, hence Borel. So A is mu-null-measurable, and mu(A) <= mu(W) < infinity. Apply the sibling upperDensity_ne_zero_outside_hausdorff_null with nu := mu and this A. It shows that the set
E_0 := {x : x ∉ A and limsup_{r -> 0+} mu(A ∩ B_r(x)) / ofReal(omega_n r^n) ≠ 0}
satisfies H^n(E_0) = 0.

5. Claim: (spt V ∩ W) \ M ⊆ E_0. Let x ∈ spt V ∩ W with x ∉ M.
(a) x ∉ A, because A ⊆ B ⊆ M.
(b) W is open and x ∈ W, so there is eps > 0 with the open ball B°_eps(x) ⊆ W. For 0 < r < eps/2, B_r(x) ⊆ B°_eps(x) ⊆ W.
(c) For such r, A ∩ B_r(x) = B_r(x) ∩ B, because B_r(x) ⊆ W. By step 3, mu(A ∩ B_r(x)) = mu(B_r(x)).
(d) By hypothesis there is c > 0 with ofReal(c omega_n r^n) <= mu(B_r(x)) for all sufficiently small r > 0. So for all sufficiently small r > 0 this holds together with r < eps/2. For such r, step 1 gives 0 < ofReal(omega_n r^n) < infinity and ofReal(c omega_n r^n) = ofReal(c) ofReal(omega_n r^n). Hence (ENNReal.le_div_iff_mul_le)
ofReal(c) <= mu(B_r(x)) / ofReal(omega_n r^n) = mu(A ∩ B_r(x)) / ofReal(omega_n r^n).
(e) The filter of right neighbourhoods of 0 is nontrivial. So a function that is eventually >= ofReal(c) is frequently >= ofReal(c). Its limsup in the complete lattice [0, infinity] is then >= ofReal(c) (le_limsup_of_frequently_le). Since c > 0, ofReal(c) > 0, so the limsup is ≠ 0. Together with (a), x ∈ E_0.

6. By step 5 and monotonicity of H^n, H^n((spt V ∩ W) \ M) <= H^n(E_0) = 0, by step 4.

## Key steps

1. omega_n > 0, so omega_n r^n > 0 for r > 0
2. The null-measurable carrier M contains a Borel set B with H^n(M \ B) = 0
3. mu(B^c) = 0 by the withDensity definition of mu, hence mu(T ∩ B) = mu(T) for all T
4. Apply the Upper Density Theorem (upperDensity_ne_zero_outside_hausdorff_null) to nu = mu and A = B ∩ W, which is measurable with mu(A) <= mu(W) < infinity
5. For x in (spt V ∩ W) \ M: x ∉ A, and for small r, mu(A ∩ B_r(x)) = mu(B_r(x)) >= ofReal(c omega_n r^n), so the limsup of the quotient is >= ofReal(c) > 0
6. Hence (spt V ∩ W) \ M lies in the H^n-null exceptional set

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean against the workspace GMT/Ch05/Contract.lean and GMT/Ch05/Submission.lean (both identical)`
- `rg -n 'def AllardHypotheses|def scaledLpNorm|def weight|def support|nullMeasurableSet_carrier|def unitBallVolume|def HasDensity' <snapshot>/project/GMT/Ch05/Contract.lean`
- `rg -n 'theorem NullMeasurableSet.exists_measurable_subset_ae_eq|theorem exists_measurable_subset_ae_eq' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `rg -n "(theorem|lemma) (measure_inter_conull|le_limsup_of_frequently_le|one_add_mul_le_pow|Ioo_mem_nhdsGT|Ioc_mem_nhdsGT|closedBall_subset_closedBall'|isOpen_iff)\b" <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem ae_eq_set|theorem convexOn_exp|theorem add_one_le_exp|theorem withDensity_apply|theorem setLIntegral_measure_zero|theorem le_of_tendsto|theorem Gamma_pos_of_pos' <snapshot>/mathlib/Mathlib`
- `rg -n 'Ioo_mem_nhdsGT|Ioc_mem_nhdsGT' <snapshot>/mathlib/Mathlib/Topology/Order/*.lean`
- `rg -l -i 'varifold|monotonicity formula' <snapshot>/mathlib/Mathlib (no match)`
- `grep -c ted_adb_ <run>/dag.json; grep -rl ted_adb_ <run>/nodes; rg -l ted_adb_ <snapshot>; git log --all -S ted_adb_ (no match in any)`
- `python3 scan of <run>/dag.json: lean_name, status, candidate_commit, lean_statement and title of aal_allard_subball_bounds, aal_monotone_quantity_ge_density, upperDensity_ne_zero_outside_hausdorff_null, aal_pinched_constants, allard52_density_bounds and the three ted_ siblings`
- `lean /tmp/adb-decomp/Checks/Types.lean; lean /tmp/adb-decomp/Checks/Assembly.lean; lean /tmp/adb-decomp/Checks/AssemblyAx.lean (#print axioms ted_allard_density_bounds_check)`
- `lean /tmp/adb-decomp/Proofs/Constants.lean; lean /tmp/adb-decomp/Proofs/ConstantsSol.lean; lean /tmp/adb-decomp-ud/CarrierReal.lean (on the Submission.lean of commit cfc18a0c)`
- `python3 -I /tmp/adb-decomp/scripts/gen_cmp.py (verifier lean_contract.validate_lean_statement and gmt-compare.child_modules in contract mode); lean /tmp/adb-decomp/cmp/*_Challenge.lean`
- `python3 -I /tmp/adb-decomp/scripts/numcheck.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Order/Ring/Pow.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Complex/Exponential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-allard-density-bounds-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-allard-density-bounds-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-tangent-plane-facts-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-pinched-density-bounds-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-pinched-density-bounds-a1-allard-subball-bounds-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-pinched-density-bounds-a1-monotone-quant-9188f1ed85/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-carrier-support-null-a1-upper-density-null-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-carrier-support-null-a1-support-diff-c-1d39650531/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/swarm-configs/588327088a8d4c038da09d29333cfb15.json`
- `/tmp/adb-decomp/Checks/Types.lean`
- `/tmp/adb-decomp/Checks/Assembly.lean`
- `/tmp/adb-decomp/Checks/AssemblyAx.lean`
- `/tmp/adb-decomp/Proofs/Constants.lean`
- `/tmp/adb-decomp/Proofs/ConstantsSol.lean`
- `/tmp/adb-decomp-ud/CarrierReal.lean`
- `/tmp/adb-decomp/scripts/numcheck.py`
- `/tmp/adb-review/FullReal.lean`

Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. Its project/GMT/Ch05/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. The contract defines weight as (μHE[n].restrict carrier).withDensity (ofReal ∘ mult) and support as U ∩ weight.support, and it has the field nullMeasurableSet_carrier.

No-match searches:
- Mathlib has no varifold or monotonicity-formula results.
- The new names ted_adb_constants and ted_adb_support_diff_carrier_null occur nowhere in dag.json, the node directories, the snapshot or git history.

Mathlib items located for the two new children (paths under the snapshot's mathlib/Mathlib):
- exists_measurable_subset_ae_eq (MeasureTheory/Measure/NullMeasurable.lean:214);
- measure_inter_conull and measure_inter_conull' (MeasureTheory/Measure/Basic.lean:308, 305);
- ae_eq_set (MeasureTheory/OuterMeasure/AE.lean:231);
- withDensity_apply (MeasureTheory/Measure/WithDensity.lean:44);
- setLIntegral_measure_zero (MeasureTheory/Integral/Lebesgue/Basic.lean:478);
- le_limsup_of_frequently_le (Order/LiminfLimsup.lean:241);
- one_add_mul_le_pow (Algebra/Order/Ring/Pow.lean:99);
- convexOn_exp (Analysis/Convex/SpecificFunctions/Basic.lean:62);
- Real.add_one_le_exp (Analysis/Complex/Exponential.lean:632);
- Real.Gamma_pos_of_pos (Analysis/SpecialFunctions/Gamma/Basic.lean:443);
- le_of_tendsto (Topology/Order/OrderClosed.lean:133);
- closedBall_subset_closedBall' and Metric.isOpen_iff (Topology/MetricSpace/Pseudo/Defs.lean:547, 833).
The regex did not match the declaration lines of Ioo_mem_nhdsGT and Ioc_mem_nhdsGT. Both are used in Topology/Order/Monotone.lean:464, and #check in the pinned environment confirmed their signatures.

Reused accepted declarations: aal_allard_subball_bounds (595bf34c), aal_monotone_quantity_ge_density (616bebf7) and upperDensity_ne_zero_outside_hausdorff_null (cfc18a0c). Each has status accepted, a candidate commit, and the exact lean_statement reused here.

Not reused: aal_pinched_constants (status rlcr-lean) and allard52_density_bounds (decomposing) are unaccepted nodes under other parents, so their names are reserved. The fresh ted_adb_constants drops aal_pinched_constants' third inequality.

Lean evidence:
- The parent's frozen type follows sorry-free from the five children plus the three siblings (AssemblyAx: only propext, Classical.choice, Quot.sound plus the named stubs).
- ted_adb_constants is proved sorry-free.
- ted_adb_support_diff_carrier_null is proved sorry-free on top of the real cfc18a0c proof.
- The reviewer's FullReal.lean contains no sorry. With all five real child proofs, the frozen parent depends only on the three standard axioms and the three siblings.
- Generated comparator challenge modules elaborate for all five children.
