# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.one_dim_sup-a1`
- Child DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.one_dim_sup-a1.cauchy_schwarz-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Non-integrable case. If g is not integrable on (-a, a), its Bochner integral there is 0 (integral_undef), and 0 <= sqrt(·) (Real.sqrt_nonneg). From now on assume g is integrable on (-a, a); then so is |g| (Integrable.abs).
2. Notation. Let I := ∫_{(-a,a)} g^2 and J := ∫_{(-a,a)} |g|. J >= 0 because the integrand is nonnegative (setIntegral_nonneg). Since g <= |g| pointwise and both are integrable, ∫_{(-a,a)} g <= J (integral_mono). The Lebesgue measure of (-a, a) is 2a (Real.volume_real_Ioo_of_le, using -a <= a), and 2a > 0.
3. Variance identity. Let m := J/(2a). Pointwise (|g(s)| - m)^2 = (g(s)^2 - 2m|g(s)|) + m^2, using |g|^2 = g^2. The three functions g^2 (hypothesis), |g| (step 1) and the constant m^2 (finite-measure set) are integrable on (-a, a). By linearity (integral_add, integral_sub, integral_const_mul, setIntegral_const):
 ∫_{(-a,a)} (|g| - m)^2 = I - 2mJ + 2a m^2 = I - J^2/a + J^2/(2a) = I - J^2/(2a).
4. Nonnegativity. The integrand (|g| - m)^2 is >= 0, so 0 <= I - J^2/(2a). Multiplying by 2a > 0 gives J^2 <= 2a I.
5. Conclusion. From step 4, J <= |J| <= sqrt(2a I) (Real.abs_le_sqrt). With step 2, ∫_{(-a,a)} g <= J <= sqrt(2a ∫_{(-a,a)} g^2).
(Equivalently, steps 2-5 are Hoelder's inequality with p = q = 2 for |g| and the constant 1, e.g. integral_mul_le_Lp_mul_Lq_of_nonneg; the elementary argument above is self-contained.)

## Key steps

1. If g is not integrable on (-a, a), the left side is 0
2. Otherwise ∫ g <= J := ∫ |g|, and the measure of (-a, a) is 2a
3. 0 <= ∫ (|g| - J/(2a))^2 = ∫ g^2 - J^2/(2a), so J^2 <= 2a ∫ g^2
4. J <= sqrt(2a ∫ g^2)

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; sha256sum GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean`
- `rg -n "theorem _root_.LipschitzOnWith.absolutelyContinuousOnInterval|theorem integral_deriv_eq_sub|ae_differentiableWithinAt_of_mem|theorem measurable_deriv |theorem stronglyMeasurable_deriv|theorem aestronglyMeasurable_deriv" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem EuclideanSpace.volume_preserving_measurableEquiv|volume_preserving_measurableEquiv|volume_preserving_funUnique|setIntegral_preimage_emb|setIntegral_image_emb|theorem MeasurePreserving.integral_comp" <snapshot>/mathlib/Mathlib`
- `rg -n "volume_preserving|measurePreserving" <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; rg -n "PiLp.volume_preserving|volume_preserving_toLp|volume_preserving_ofLp" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem norm_deriv_le_of_lipschitzOn|theorem norm_fderiv_le_of_lipschitzOn|theorem integral_mul_le_Lp_mul_Lq_of_nonneg|theorem integral_Icc_eq_integral_Ioo|theorem setIntegral_mono_set|theorem norm_integral_le_integral_norm_uIoc|theorem abs_integral_le_integral_abs|intervalIntegrable_deriv" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem EuclideanSpace\.(norm_single|dist_single|single_apply)|def single|single_sub|EuclideanSpace.proj" <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean <snapshot>/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `rg -n "integrableOn_of_bounded|IntegrableOn.of_bound|volume_real_Ioo|theorem volume_Ioo|setIntegral_mono_on|theorem setIntegral_const|ContinuousOn.integrableOn_compact|integrableOn_const|integrableOn_Ioc_iff_integrableOn_Ioo|memLp_two_iff_integrable_sq" <snapshot>/mathlib/Mathlib`
- `python3 -I: list id/lean_name/status of all 379 nodes in <run>/dag.json; filter names containing ods/one_dim/interval/ftc/deriv; print allard52_lad_lipschitz_ftc and related nodes`
- `grep -c / rg -l for tdo_ods_ball_integral_eq_interval, tdo_ods_hsNormSq_fderiv_single, tdo_ods_norm_sub_le_integral_deriv, tdo_ods_integral_le_sqrt, tdo_ods_interval_sup_le in <run>/dag.json <run>/nodes <snapshot>/project <snapshot>/mathlib/Mathlib GMT .lake/packages/simongmt/Poincare (no match)`
- `git show dd3aca16:GMT/Ch05/Submission.lean (accepted sibling layout: namespace Submission); git show <accepted aal_tangent_structure branch>:GMT/Ch05/Submission.lean | grep ^import (imports extended to 21)`
- `lake env lean -o /tmp/ods-decomp/olean/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean; lean /tmp/ods-decomp/checks/Avail.lean (AC lemmas absent from frozen import closure; Rademacher, measurable_deriv, PiLp.volume_preserving_toLp present)`
- `lean /tmp/ods-decomp/checks/Assembly.lean; ChildA/ChildB/ChildC1/ChildC2/ChildC.lean; /tmp/ods-decomp/final/StatementsOnly.lean; /tmp/ods-decomp/final/Full.lean (generated from the final JSON lean_statements)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-one-dim-sup-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-one-dim-sup-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/problem.md`
- `/tmp/ods-decomp/checks/Avail.lean`
- `/tmp/ods-decomp/checks/Assembly.lean`
- `/tmp/ods-decomp/checks/ChildA.lean`
- `/tmp/ods-decomp/checks/ChildB.lean`
- `/tmp/ods-decomp/checks/ChildC1.lean`
- `/tmp/ods-decomp/checks/ChildC2.lean`
- `/tmp/ods-decomp/checks/ChildC.lean`
- `/tmp/ods-decomp/final/StatementsOnly.lean`
- `/tmp/ods-decomp/final/Full.lean`

**Snapshot.** a7f8fcd21d5c8fc7 pins project ea5607598f… and Mathlib 25730c7c759d…. Its Contract.lean is byte-identical (sha256 c966f51e…) to the workspace Contract.lean and Submission.lean.

**Declarations located (paths under mathlib/Mathlib):**
- Change of variables (ball_integral):
  - PiLp.volume_preserving_toLp (MeasureTheory/Measure/Haar/InnerProductSpace.lean:139).
  - volume_preserving_funUnique (MeasureTheory/Constructions/Pi.lean:845).
  - MeasurePreserving.setIntegral_preimage_emb (MeasureTheory/Integral/Bochner/Set.lean:571).
  - EuclideanSpace.single is an abbrev for PiLp.single 2 (Analysis/InnerProductSpace/PiL2.lean:296; PiLp.lean:152), and its norm lemmas are simp lemmas.
- FTC bound (ftc_bound):
  - LipschitzOnWith.absolutelyContinuousOnInterval (MeasureTheory/Function/AbsolutelyContinuous.lean:309).
  - AbsolutelyContinuousOnInterval.integral_deriv_eq_sub (MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean:225).
  - AbsolutelyContinuousOnInterval.intervalIntegrable_deriv (MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean:160).
  - LipschitzOnWith.ae_differentiableWithinAt_of_mem (Analysis/Calculus/Rademacher.lean:361).
  - measurable_deriv (Analysis/Calculus/FDeriv/Measurable.lean:398).
  - norm_deriv_le_of_lipschitzOn (Analysis/Calculus/Deriv/Basic.lean:932).
  - intervalIntegral.norm_integral_le_integral_norm_uIoc (MeasureTheory/Integral/IntervalIntegral/Basic.lean:738).
  - integral_Icc_eq_integral_Ioo (MeasureTheory/Integral/Bochner/Set.lean:718) and setIntegral_mono_set (:737).
  - integrableOn_Ioc_iff_integrableOn_Ioo (MeasureTheory/Integral/IntegrableOn.lean:956). Its first argument is an auto-param, so `.mpr` must be applied after supplying it.
- Cauchy–Schwarz (cauchy_schwarz):
  - Real.volume_real_Ioo_of_le (MeasureTheory/Measure/Lebesgue/Basic.lean:106).
  - Measure.integrableOn_of_bounded (MeasureTheory/Integral/IntegrableOn.lean:716).
  - integral_mul_le_Lp_mul_Lq_of_nonneg (MeasureTheory/Integral/Bochner/Basic.lean:1230), as an alternative route.

**Import closure.** The frozen header's imports provide Rademacher, measurable_deriv, the volume-preserving lemmas and norm_deriv_le_of_lipschitzOn. They do NOT provide LipschitzOnWith.absolutelyContinuousOnInterval, AbsolutelyContinuousOnInterval.integral_deriv_eq_sub or intervalIntegrable_deriv (checked in Avail.lean). Proving ftc_bound therefore needs `import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun`. Accepted sibling branches already add Submission imports, for example the aal_tangent_structure branch, which has 21 imports.

**DAG.**
- No node with an identical statement exists.
- allard52_lad_lipschitz_ftc needs a continuous derivative and is still decomposing, so it is not reusable.
- The five new tdo_ods_* names occur nowhere in dag.json, the node directories, the snapshot, GMT/ or simongmt.

**Lean results.**
- StatementsOnly.lean: all five frozen lean_statements elaborate after `import GMT.Ch05.Submission` in namespace GMT.Ch05.Submission. The only warnings are the expected `sorry` ones.
- Full.lean (frozen header plus the AC import, generated from the final JSON statements):
  - All five children have complete proofs.
  - The frozen parent tdo_one_dim_sup_le is proved from ball_integral, hs_deriv and interval_sup.
  - interval_sup is proved from ftc_bound and cauchy_schwarz.
  - `#print axioms` reports only [propext, Classical.choice, Quot.sound] for all six declarations.
