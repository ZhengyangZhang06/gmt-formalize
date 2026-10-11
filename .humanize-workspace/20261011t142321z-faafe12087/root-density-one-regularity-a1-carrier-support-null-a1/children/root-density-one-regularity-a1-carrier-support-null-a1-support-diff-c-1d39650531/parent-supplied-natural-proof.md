# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_regularity-a1.carrier_support_null-a1`
- Child DAG node: `root.density_one_regularity-a1.carrier_support_null-a1.support_diff_carrier_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1(a) and 3 of the parent proof (Simon Ch. 4, Remark 4.10(1)). The Upper Density Theorem (Simon Ch. 1, 3.6) is supplied by sibling upper_density_null (Lean name upperDensity_ne_zero_outside_hausdorff_null).

Notation: H^n = muHE[n] on X = R^(n+l); M = V.carrier; mu = V.weight = (H^n restricted to M) with density ofReal(theta); spt V = U ∩ spt mu; B_r are closed balls and B'_r open balls. V.HasDensity x t means mu(B_r(x)) / ofReal(omega_n r^n) -> ofReal(t) in [0, infinity] as r -> 0+, with omega_n = unitBallVolume n. No openness of U and no lower bound on n is used.

1. Basic facts.
   (a) mu << H^n restricted to M (withDensity_absolutelyContinuous). Also (H^n restricted to M)(X \ M) = H^n((X \ M) ∩ M) = H^n(∅) = 0 (Measure.restrict_apply₀', M H^n-null-measurable). Hence mu(X \ M) = 0, and consequently mu(S ∩ M) = mu(S) for every set S (measure_inter_conull).
   (b) M is mu-null-measurable. It is H^n-null-measurable; H^n restricted to M ≤ H^n, so H^n restricted to M << H^n; and mu << H^n restricted to M (NullMeasurableSet.mono_ac).
2. Finite-mass radii. Let N := spt V \ M and x ∈ N. As x ∈ spt V, the hypothesis gives t with mu(B_r(x))/ofReal(omega_n r^n) -> ofReal(t) as r -> 0+. Since ofReal(t) < infinity, the quotient is < infinity for all sufficiently small r > 0, because [0, infinity) is a neighbourhood of ofReal(t). Choose such an r_x > 0. Then mu(B_{r_x}(x)) < infinity: otherwise the quotient would be infinity / ofReal(omega_n r_x^n) = infinity, as the denominator is finite (ENNReal.top_div_of_ne_top).
3. Countable subcover. The open balls B'_{r_x}(x), x ∈ N, cover N, since x ∈ B'_{r_x}(x) as r_x > 0. R^(n+l) is second countable, so there is a countable T ⊆ N such that the union of B'_{r_y}(y) over y ∈ T equals the union of B'_{r_x}(x) over x ∈ N (TopologicalSpace.isOpen_biUnion_countable). Hence N ⊆ union over y ∈ T of (N ∩ B'_{r_y}(y)). By countable subadditivity (measure_biUnion_null_iff) it suffices to prove H^n(N ∩ B'_{r_y}(y)) = 0 for each y ∈ T.
4. Fix y ∈ T and put A := M ∩ B_{r_y}(y). A is mu-null-measurable, by 1(b) and because closed balls are Borel. Also mu(A) <= mu(B_{r_y}(y)) < infinity by step 2, since y ∈ N. By sibling upper_density_null applied to nu := mu and this A, the set E_y := {x : x ∉ A and limsup_{rho -> 0+} mu(A ∩ B_rho(x))/ofReal(omega_n rho^n) ≠ 0} has H^n(E_y) = 0.
5. N ∩ B'_{r_y}(y) ⊆ E_y. Let x ∈ N ∩ B'_{r_y}(y).
   (i) x ∉ M, hence x ∉ A.
   (ii) Since B'_{r_y}(y) is open, there is eps > 0 with B'_eps(x) ⊆ B'_{r_y}(y). For 0 < rho < eps we have B_rho(x) ⊆ B'_eps(x) ⊆ B'_{r_y}(y) ⊆ B_{r_y}(y). So A ∩ B_rho(x) = B_rho(x) ∩ M, and by 1(a), mu(A ∩ B_rho(x)) = mu(B_rho(x)). Thus the quotients mu(A ∩ B_rho(x))/ofReal(omega_n rho^n) and mu(B_rho(x))/ofReal(omega_n rho^n) agree for all rho ∈ (0, eps), a set in the filter of right neighbourhoods of 0.
   (iii) As x ∈ spt V, the hypothesis gives t > 0 with mu(B_rho(x))/ofReal(omega_n rho^n) -> ofReal(t). By (ii) the A-quotient has the same limit (Tendsto.congr'). Along the nontrivial filter of right neighbourhoods of 0, the limsup of a convergent function is its limit (Tendsto.limsup_eq). So the limsup equals ofReal(t), which is ≠ 0 because t > 0. Hence x ∈ E_y.
6. Therefore H^n(N ∩ B'_{r_y}(y)) <= H^n(E_y) = 0 for every y ∈ T, and by step 3, H^n(spt V \ M) = H^n(N) = 0.

## Key steps

1. mu vanishes off M (mu << H^n restricted to M) and M is mu-null-measurable
2. Positive finite density at each x ∈ N = spt V \ M gives r_x > 0 with mu(B_{r_x}(x)) < infinity
3. Second countability: countably many open balls B'_{r_y}(y), y ∈ T ⊆ N, cover N, reducing to each N ∩ B'_{r_y}(y)
4. Apply sibling upper_density_null to nu = mu and A = M ∩ B_{r_y}(y), which is null-measurable with finite mass
5. For x ∈ N ∩ B'_{r_y}(y): x ∉ A and mu(A ∩ B_rho(x)) = mu(B_rho(x)) for small rho, so the limsup equals ofReal(t) > 0 and x lies in the H^n-null exceptional set

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
