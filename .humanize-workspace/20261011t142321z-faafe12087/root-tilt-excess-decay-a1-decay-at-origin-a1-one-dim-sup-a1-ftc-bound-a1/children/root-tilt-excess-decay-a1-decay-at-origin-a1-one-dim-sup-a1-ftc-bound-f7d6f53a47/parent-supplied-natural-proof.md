# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.one_dim_sup-a1.ftc_bound-a1`
- Child DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.one_dim_sup-a1.ftc_bound-a1.interval_dominated_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Inclusion. uIoc s t is contained in (-a, a]. Indeed, if r is in uIoc s t (mem_uIoc), then either s < r <= t or t < r <= s. In the first case -a <= s < r and r <= t <= a. In the second case -a <= t < r and r <= s <= a. In both cases -a < r <= a.
2. Integrability of h. The singleton {a} is Lebesgue-null and h(a) is a finite real number. So h is integrable on (-a, a] iff it is integrable on (-a, a) (integrableOn_Ioc_iff_integrableOn_Ioo). By hypothesis h is integrable on (-a, a), so by this equivalence it is integrable on (-a, a]; therefore, by step 1, it is integrable on uIoc s t (IntegrableOn.mono_set).
3. Integrability of |g|. g is interval integrable between s and t, i.e. integrable on uIoc s t (intervalIntegrable_iff). Hence |g| = ||g|| is integrable on uIoc s t (Integrable.norm).
4. Domination on (-a, a]. For almost every r we have r ≠ a (Measure.ae_ne), and also the hypothesis 'r in (-a, a) implies |g(r)| <= h(r)'. For such r with r in (-a, a], we get r < a, so r is in (-a, a) and hence |g(r)| <= h(r). Thus, for a.e. r: r in (-a, a] implies |g(r)| <= h(r). In particular 0 <= |g(r)| <= h(r) for a.e. r in (-a, a], i.e. h >= 0 almost everywhere for Lebesgue measure restricted to (-a, a] (ae_restrict_iff', measurableSet_Ioc).
5. Chain of inequalities:
 ∫_s^t g <= |∫_s^t g| = ||∫_s^t g|| (le_abs_self, Real.norm_eq_abs)
 <= ∫_{uIoc s t} ||g|| (intervalIntegral.norm_integral_le_integral_norm_uIoc)
 <= ∫_{uIoc s t} h (setIntegral_mono_on_ae: both integrands are integrable on uIoc s t by steps 3 and 2, uIoc s t is measurable (measurableSet_uIoc), and for a.e. r in uIoc s t we have r in (-a, a] by step 1, so ||g(r)|| = |g(r)| <= h(r) by step 4)
 <= ∫_{(-a,a]} h (setIntegral_mono_set: h is integrable on (-a, a] by step 2, h >= 0 a.e. on (-a, a] by step 4, and uIoc s t is contained in (-a, a] by step 1)
 = ∫_{(-a,a)} h (integral_Ioc_eq_integral_Ioo; Lebesgue measure has no atoms).
 This is the claim.
Remark (Lean implementation): every lemma cited is in the import closure of the frozen header, so no new import is needed.

## Key steps

1. uIoc s t is contained in (-a, a] because s, t are in [-a, a]
2. h is integrable on (-a, a] (null endpoint) and on uIoc s t; ||g|| is integrable on uIoc s t (intervalIntegrable_iff)
3. with Measure.ae_ne for a: |g| <= h a.e. on (-a, a], hence h >= 0 a.e. there
4. ∫_s^t g <= |∫_s^t g| <= ∫_{uIoc s t} |g| <= ∫_{uIoc s t} h <= ∫_{(-a,a]} h = ∫_{(-a,a)} h

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json (project ea5607598f31, mathlib 25730c7c759d)`
- `rg -n "theorem _root_.LipschitzOnWith.absolutelyContinuousOnInterval" <snapshot>/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean; rg -n "integral_deriv_eq_sub|intervalIntegrable_deriv" <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `rg -n "(theorem|lemma) +(norm_deriv_le_of_lipschitzOn|measurable_deriv|ae_differentiableWithinAt_of_mem|Measure\.integrableOn_of_bounded|setIntegral_mono_on_ae|setIntegral_mono_set|integral_Ioc_eq_integral_Ioo|integrableOn_Ioc_iff_integrableOn_Ioo|HasDerivAt\.inner|abs_real_inner_le_norm|norm_integral_le_integral_norm_uIoc|measure_Ioo_lt_top|intervalIntegrable_iff)( |$)" <snapshot>/mathlib/Mathlib`
- `lake env lean -o /tmp/ftcb-decomp/olean/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean; lean /tmp/ftcb-decomp/checks/Avail.lean and Sigs.lean (#check of every cited lemma after import GMT.Ch05.Submission)`
- `python3 -I: dag.json statuses, the one_dim_sup subtree, regex search for similar statements (IntegrableOn (fun _ => ‖deriv, deriv (fun _ => inner, IntervalIntegrable, ...)), lean_names allard52_lad_lipschitz_ftc / allard52_tangent_ae / lgc_tangent_plane_ae / ted_tangent_plane_facts / aal_tangent_structure`
- `rg -l -F <name> <run>/dag.json <run>/nodes <snapshot>/project <snapshot>/mathlib/Mathlib GMT .lake/packages/simongmt/Poincare .humanize/math-wiki; git log --all -S<name> for tdo_ods_integrableOn_norm_deriv, tdo_ods_ae_abs_deriv_inner_le, tdo_ods_intervalIntegral_le_of_ae_abs_le (no match)`
- `grep -rhoi 'leaf gate' <run>/nodes and .humanize/math-wiki ('import closure', 'AbsolutelyContinuousFun'); git show d715896f (lipschitz_ftc deviation); git show 9f4dca65 / 55e098f5 / a8902dc6 -- GMT/Ch05/Submission.lean | grep -c '^+import' (6 each)`
- `read check_source_delta in /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py and check_parent_git_delta in parent_verification.py; python3 -I /tmp/ftcb-review/scripts/leafgate.py (children PASS; whole node with AC import FAIL)`
- `python3 -I: gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch05.main_theorem') for the comparator child scope; read .humanize/swarm-configs/42724b071e414e11afdd6da8fa97f1bb.json (max_depth 6, max_children 12, max_nodes 1000)`
- `lean /tmp/ftcb-decomp/checks/Children.lean, Glue.lean, GlueStubs.lean; /tmp/ftcb-decomp/final/StatementsOnly.lean; lake env lean --root=/tmp/ftcb-decomp/sim -o ... /tmp/ftcb-decomp/sim/GMT/Ch05/Submission.lean; lean /tmp/ftcb-decomp/final/NodeSolutionSim.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-one-dim-sup-a1-ftc-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-one-dim-sup-a1-ftc-bound-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-one-dim-sup-a1-ftc-bound-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/swarm-configs/42724b071e414e11afdd6da8fa97f1bb.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/parent_verification.py`
- `/tmp/ftcb-decomp/checks/Avail.lean`
- `/tmp/ftcb-decomp/checks/Sigs.lean`
- `/tmp/ftcb-decomp/checks/Children.lean`
- `/tmp/ftcb-decomp/checks/Glue.lean`
- `/tmp/ftcb-decomp/checks/GlueStubs.lean`
- `/tmp/ftcb-decomp/final/StatementsOnly.lean`
- `/tmp/ftcb-decomp/final/NodeSolutionSim.lean`
- `/tmp/ftcb-decomp/sim/GMT/Ch05/Submission.lean`
- `/tmp/ftcb-review/scripts/leafgate.py`

**Snapshot.** a7f8fcd21d5c8fc7 pins project ea5607598f31 and Mathlib 25730c7c759d.

**Lemma locations (snapshot Mathlib).**
- Outside the frozen import closure (all three report unknown constant/identifier after import GMT.Ch05.Submission):
  - LipschitzOnWith.absolutelyContinuousOnInterval (MeasureTheory/Function/AbsolutelyContinuous.lean:309).
  - AbsolutelyContinuousOnInterval.integral_deriv_eq_sub (IntervalIntegral/AbsolutelyContinuousFun.lean:225).
  - AbsolutelyContinuousOnInterval.intervalIntegrable_deriv (IntervalIntegral/DerivIntegrable.lean:160).
- Inside the closure, and used by the children:
  - measurable_deriv (FDeriv/Measurable.lean:398) and norm_deriv_le_of_lipschitzOn (Deriv/Basic.lean:932).
  - LipschitzOnWith.ae_differentiableWithinAt_of_mem (Rademacher.lean:361).
  - Measure.integrableOn_of_bounded (IntegrableOn.lean:716) and integrableOn_Ioc_iff_integrableOn_Ioo (:956).
  - integral_Ioc_eq_integral_Ioo, setIntegral_mono_set and setIntegral_mono_on_ae (Bochner/Set.lean:709, 737, 766).
  - intervalIntegrable_iff and norm_integral_le_integral_norm_uIoc (IntervalIntegral/Basic.lean:86, 738).
  - HasDerivAt.inner (InnerProductSpace/Calculus.lean:109) and abs_real_inner_le_norm (InnerProductSpace/Basic.lean:471).
  - measure_Ioo_lt_top (Typeclasses/Finite.lean:661).

**Gates.**
- Leaf gate (check_source_delta): requires the frozen base byte-for-byte, exactly one theorem, and no import. On this whole node with the AC import it reports 'leaf proof must preserve the complete frozen base byte-for-byte'.
- Parent gate (check_parent_git_delta): restricts only which files change.
- Precedents: accepted parents 55e098f5, 9f4dca65 and a8902dc6 each add 6 imports. The accepted leaf allard52_lad_lipschitz_ftc requires ContinuousOn k, so it is not reusable here.

**Reuse and names.** No DAG node has an identical statement. The three new names occur nowhere.

**Lean results.**
- The three children prove in the frozen closure, and each passes the leaf gate.
- The glue, with the AC import, proves the parent from the children and also from sorry'd children.
- A simulated full Submission.lean compiles.
- Comparator-form challenge and solution checks pass for all four declarations, with axioms [propext, Classical.choice, Quot.sound].
