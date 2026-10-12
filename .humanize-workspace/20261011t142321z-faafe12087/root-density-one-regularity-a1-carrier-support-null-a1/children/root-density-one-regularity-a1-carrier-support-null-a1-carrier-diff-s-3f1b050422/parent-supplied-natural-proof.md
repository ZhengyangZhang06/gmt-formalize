# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_regularity-a1.carrier_support_null-a1`
- Child DAG node: `root.density_one_regularity-a1.carrier_support_null-a1.carrier_diff_support_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1(b) and 2 of the parent proof (Simon Ch. 4, Remark 4.10(1): spt V versus the carrier M).

Notation: H^n = muHE[n] on X = R^(n+l); M = V.carrier ⊆ U; theta = V.mult; mu = V.weight = (H^n restricted to M) with density x -> ofReal(theta(x)) (Mathlib withDensity); spt mu = V.weight.support, the points all of whose neighbourhoods have positive mu-measure; spt V = U ∩ spt mu. No density hypothesis, no openness of U and no restriction on n is used.

1. Reduction. Let O := X \ spt mu. If x ∈ M \ spt V, then x ∉ spt mu. Otherwise x ∈ U (because M ⊆ U, field carrier_subset) and x ∈ spt mu, so x ∈ U ∩ spt mu = spt V, a contradiction. Hence M \ spt V ⊆ O ∩ M, and by monotonicity it suffices to prove H^n(O ∩ M) = 0.
2. O is open, because spt mu is closed (Measure.isClosed_support). In particular O is a Borel (measurable) set.
3. mu(O) = 0. Every point of O has an open neighbourhood of mu-measure 0, by definition of the support. X is second countable, hence hereditarily Lindelof, so countably many of these neighbourhoods cover O. Countable subadditivity gives mu(O) = 0 (Measure.measure_compl_support).
4. Since O is measurable, mu(O) = ∫_O ofReal(theta) d(H^n restricted to M) (withDensity_apply). Also (H^n restricted to M) restricted to O equals H^n restricted to O ∩ M (Measure.restrict_restrict, O measurable). Hence ∫ ofReal(theta) d(H^n restricted to O ∩ M) = 0.
5. The function x -> ofReal(theta(x)) is a.e.-measurable for H^n restricted to O ∩ M. Indeed, theta is a.e.-measurable for H^n restricted to M (field aemeasurable_mult); H^n restricted to O ∩ M ≤ H^n restricted to M since O ∩ M ⊆ M (Measure.restrict_mono); and ofReal preserves a.e.-measurability. A nonnegative a.e.-measurable function with zero integral vanishes almost everywhere (lintegral_eq_zero_iff'). So ofReal(theta(x)) = 0 for almost every x with respect to H^n restricted to O ∩ M.
6. O ∩ M is H^n-null-measurable, since O is open and M is H^n-null-measurable (field nullMeasurableSet_carrier). Therefore (ae_restrict_iff'₀), for H^n-a.e. x: if x ∈ O ∩ M then ofReal(theta(x)) = 0, i.e. theta(x) ≤ 0.
7. But theta(x) > 0 for every x ∈ M (field mult_pos). Hence for H^n-a.e. x we have x ∉ O ∩ M. That is, the complement of O ∩ M is H^n-conull, so H^n(O ∩ M) = 0 (mem_ae_iff).
8. By step 1 and monotonicity, H^n(M \ spt V) ≤ H^n(O ∩ M) = 0.

## Key steps

1. M \ spt V ⊆ O ∩ M with O = complement of spt mu, because M ⊆ U and spt V = U ∩ spt mu
2. O is open and mu(O) = 0 by second countability (Measure.measure_compl_support)
3. withDensity on the measurable set O: the integral of ofReal(theta) against H^n restricted to O ∩ M is 0, so theta ≤ 0 H^n-a.e. on O ∩ M
4. theta > 0 on M forces H^n(O ∩ M) = 0, hence H^n(M \ spt V) = 0

## Reference use

### local-project

Queries:
- `sed -n 1,463p GMT/Ch05/Contract.lean; diff GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean`
- `grep -n '^theorem ' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean; sed -n 1,140p and 240,420p of that file (simon_theorem_3_3, simon_theorem_3_6, mul_simonHausdorff_le_of_le_dimensionalUpperDensity)`
- `grep -n '^theorem \|^def \|^noncomputable def \|^abbrev ' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/{Densities,Hausdorff,Basic,EuclideanNormalization}.lean; sed -n 25,60p Densities.lean; sed -n 1,60p,260,300p,405,600p Hausdorff.lean; sed -n 200,440p Basic.lean`
- `sed -n 1,140p <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure_def, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero)`
- `grep -n for measure_compl_support, isClosed_support, lintegral_eq_zero_iff', ae_restrict_iff'₀, measure_inter_conull, measure_inter_add_sdiff₀, isOpen_biUnion_countable, top_div_of_ne_top, withDensity_absolutelyContinuous, withDensity_apply, restrict_apply₀', restrict_restrict, Filter.Tendsto.limsup_eq, Real.Gamma_pos_of_pos, ENNReal.ofReal_pow, ENNReal.rpow_natCast, ENNReal.div_ne_zero in <snapshot>/mathlib/Mathlib`
- `sed -n 590,735p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt (Simon 3.3-3.7 statements and printed proofs)`
- `python3 -I scan of dag.json lean_name/lean_statement fields; grep -rl for hausdorff_carrier_diff_support_null, upperDensity_ne_zero_outside_hausdorff_null, hausdorff_support_diff_carrier_null in dag.json, nodes/, GMT/, .lake/packages/simongmt/Poincare`
- `lake env lean /tmp/csn-a1-check/Check1.lean (contract lines 1-460 + 3 children as sorry + parent proof)`
- `lake env lean /tmp/csn-a1-check/Check2.lean (+ import Poincare.SimonGMT.Chapter01.DensityComparison; sorry-free proofs of all three children and of the parent; #print axioms)`
- `lake env lean /tmp/csn-a1-check/Check3.lean (comparator-style: each frozen type at GMT.Ch05 scope closed by exact Submission.X; #print axioms)`
- `python3 -I /tmp/csn-a1-check/validate.py verifier/lean_contract.py (validate_lean_statement on the 3 child statements)`
- `sed -n 300,620p verifier/gmt-compare.py (frozen-input byte checks, child NodeChallenge/NodeSolution generation)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-carrier-support-null-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-carrier-support-null-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/csn-a1-check/Check1.lean`
- `/tmp/csn-a1-check/Check2.lean`
- `/tmp/csn-a1-check/Check3.lean`

Snapshot: project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). The snapshot Contract.lean is byte-identical to the workspace Contract.lean (cmp), and the workspace Submission.lean equals the Contract.

No prior work: none of the three proposed names occurs in dag.json, nodes/, GMT/ or the simongmt sources, and none of them is reserved by another DAG branch.

SimonGMT supplies the analytic core:
- simon_theorem_3_6 (Upper Density Theorem; Chapter01/DensityComparison.lean:332) and simon_theorem_3_3 / mul_simonHausdorff_le_of_le_dimensionalUpperDensity (lines 294, 251). They hold for an arbitrary OuterMeasure on a metric space, every real n >= 0, with IsBorelRegularOuterMeasure, a Caratheodory-measurable A and finite mass.
- dimensionalUpperDensity / dimensionalDensityQuotient (Densities.lean:44/39).
- realUnitBallVolume (Hausdorff.lean:34) is definitionally ofReal(unitBallVolume n).
- simonHausdorffOuterMeasureReal_eq_scaled_hausdorffMeasure (Hausdorff.lean:424) and realUnitBallVolume_pos (499).
- measure_toOuterMeasure_isBorelRegular and isCaratheodoryMeasurable_restrict (Basic.lean:309/43).
These are stated in SimonGMT's own normalization, so a bridge to μHE[n] is needed. It is child upper_density_null, transported via Mathlib's euclideanHausdorffMeasure_def (Measure.lean:74). DensityComparison is not imported by the contract, so Submission must add `import Poincare.SimonGMT.Chapter01.DensityComparison`. gmt-compare.py byte-checks only the frozen inputs, so this is allowed.

Mathlib lemmas confirmed in the snapshot:
- Measure.measure_compl_support and isClosed_support (Support.lean:202, 115)
- isOpen_biUnion_countable (Topology/Bases.lean:942)
- lintegral_eq_zero_iff' (Lebesgue/Basic.lean:322)
- measure_inter_conull (Measure/Basic.lean:308)
- measure_inter_add_sdiff₀ (NullMeasurable.lean:265)
- withDensity_apply and withDensity_absolutelyContinuous (WithDensity.lean:44, 146)
- restrict_apply₀', restrict_restrict and ae_restrict_iff'₀ (Restrict.lean:136, 205, 624)
- Filter.Tendsto.limsup_eq (Topology/Order/LiminfLimsup.lean:190)

Simon's printed proof of 3.6 (chapter-01.txt l.700-722) is copied into upper_density_null.

Lean checks: Check1, Check2 and Check3 compile as described in the rationale. All three children and the parent have sorry-free proofs with axioms propext, Classical.choice, Quot.sound. The comparator-style elaboration of every frozen child type succeeds.
