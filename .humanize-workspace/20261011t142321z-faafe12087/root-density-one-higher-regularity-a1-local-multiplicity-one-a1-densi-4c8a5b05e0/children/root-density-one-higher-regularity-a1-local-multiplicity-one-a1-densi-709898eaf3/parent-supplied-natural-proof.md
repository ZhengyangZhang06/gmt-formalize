# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.local_multiplicity_one-a1.density_eq_mult_ae-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.local_multiplicity_one-a1.density_eq_mult_ae-a1.weight_restrict_withdensity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2-3 of the parent-supplied proof (mu vanishes off its support, and lambda = mu restricted to O is H^n restricted to Sigma cap O with density f), stated for an arbitrary measurable O contained in U.
Notation: H^n := muHE[n]; M := V.carrier; theta := V.mult; mu := V.weight = (H^n restricted to M).withDensity (ofReal o theta); spt mu := mu.support; Sigma := V.support = U cap spt mu; A := Sigma cap O; f(x) := ofReal(M.indicator theta x).
1. A = spt mu cap O, and A is measurable. If x is in A, then x is in spt mu and in O. Conversely, if x is in spt mu cap O, then x is in U (O is contained in U), so x is in U cap spt mu = Sigma and hence in A. The support spt mu is closed (Measure.isClosed_support), hence Borel, and O is measurable, so A is measurable.
2. mu((spt mu)^c) = 0 by Measure.measure_compl_support (R^(n+l) is second countable, hence hereditarily Lindelof).
3. By Measure.ext it suffices to prove (mu restricted to O)(S) = ((H^n restricted to A).withDensity f)(S) for every measurable set S. Fix a measurable S. Then S cap A is measurable by step 1.
4. Left side. (mu restricted to O)(S) = mu(S cap O) by Measure.restrict_apply (S measurable). We show mu(S cap O) = mu(S cap A).
- S cap A is contained in S cap O, so mu(S cap A) <= mu(S cap O).
- S cap O is contained in (S cap A) union (spt mu)^c. A point of S cap O either lies in spt mu, hence in S cap (spt mu cap O) = S cap A by step 1, or lies in (spt mu)^c. So mu(S cap O) <= mu(S cap A) + mu((spt mu)^c) = mu(S cap A) by step 2.
5. By the definition of mu, withDensity_apply (S cap A measurable) and Measure.restrict_restrict (S cap A measurable): mu(S cap A) = lintegral over S cap A of ofReal(theta) d(H^n restricted to M) = lintegral of ofReal(theta) d(H^n restricted to ((S cap A) cap M)).
6. Right side. By withDensity_apply and Measure.restrict_restrict (S measurable): ((H^n restricted to A).withDensity f)(S) = lintegral over S of f d(H^n restricted to A) = lintegral of f d(H^n restricted to (S cap A)).
7. Pointwise, f = M.indicator (ofReal o theta). For x in M both sides equal ofReal(theta x); for x not in M both equal ofReal(0) = 0.
8. M is H^n-null-measurable (structure field nullMeasurableSet_carrier). Since H^n restricted to (S cap A) <= H^n, M is also null-measurable for H^n restricted to (S cap A). Therefore:
- by lintegral_indicator_0, lintegral of M.indicator (ofReal o theta) d(H^n restricted to (S cap A)) = lintegral over M of ofReal(theta) d(H^n restricted to (S cap A));
- by Measure.restrict_restrict_0, (H^n restricted to (S cap A)) restricted to M = H^n restricted to (M cap (S cap A)).
9. Conclusion. M cap (S cap A) = (S cap A) cap M, so steps 4-8 give (mu restricted to O)(S) = lintegral of ofReal(theta) d(H^n restricted to ((S cap A) cap M)) = ((H^n restricted to A).withDensity f)(S). Since S was an arbitrary measurable set, mu restricted to O = (H^n restricted to (Sigma cap O)).withDensity f.

## Key steps

1. Sigma cap O = spt mu cap O is measurable (O contained in U, spt mu closed)
2. mu((spt mu)^c) = 0, hence mu(S cap O) = mu(S cap Sigma cap O)
3. left side = integral of ofReal(theta) over H^n restricted to ((S cap A) cap M), by withDensity_apply and restrict_restrict
4. right side = integral of f over H^n restricted to (S cap A), with f = 1_M ofReal(theta); lintegral_indicator_0 and restrict_restrict_0 use the null-measurability of M
5. the measures agree on every measurable S, so they are equal (Measure.ext)

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean`
- `rg -l 'dohr_lmo_dema|lmo_dema' <snapshot>/project GMT .humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json .lake/packages/simongmt`
- `python3 -I scan of dag.json: lean_name list (dohr/density/withDensity) and lean_statement containing withDensity, rnDeriv, IsLocallyFiniteMeasure, IsFiniteMeasure, weight finiteness (< ⊤) or indicator`
- `rg -n 'theorem ae_tendsto_rnDeriv|theorem ae_tendsto_lintegral_div|theorem ae_tendsto_measure_inter_div|withDensity' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `rg -n '^theorem ae_tendsto_rnDeriv \(|^theorem rnDeriv_withDensity₀|^lemma measure_compl_support|^lemma isClosed_support|^theorem lintegral_indicator₀|^theorem restrict_restrict₀|^theorem aemeasurable_indicator_iff₀|^theorem measure_closedBall_lt_top|^protected theorem Tendsto.mul |^theorem withDensity_absolutelyContinuous |^theorem ae_restrict_iff. |^theorem ae_restrict_mem₀|^theorem ofReal_le_enorm|instHasBesicovitchCovering|sigmaFinite_of_locallyFinite' over the corresponding <snapshot>/mathlib files`
- `rg -n 'ofReal_le_enorm|enorm_eq_ofReal_abs' <snapshot>/mathlib/Mathlib`
- `python3 -I: contract_scope(Contract.lean, 'GMT.Ch05.main_theorem') from verifier/gmt-compare.py and validate_lean_statement from verifier/lean_contract.py on the two child types and the parent type`
- `lake env lean -o /tmp/dema-split-k7q2/build/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean`
- `lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/dema-split-k7q2/build lean /tmp/dema-split-k7q2/src/T0.lean' (lemma signatures; HasBesicovitchCovering, SecondCountableTopology, BorelSpace, ProperSpace, sigma-finiteness instances on Amb n l)`
- `lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/dema-split-k7q2/build lean /tmp/dema-split-k7q2/src/Full.lean' (both children fully proved + parent assembled; #print axioms)`
- `lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/dema-split-k7q2/build lean /tmp/dema-split-k7q2/src/Assembly.lean' (parent from sorry-stub children)`
- `lake env lean --root=/tmp/dema-split-k7q2/sub2 -o /tmp/dema-split-k7q2/build2/GMT/Ch05/Submission.olean /tmp/dema-split-k7q2/sub2/GMT/Ch05/Submission.lean; lean /tmp/dema-split-k7q2/cmp/{Challenge,Solution}{A,B,P}.lean (comparator-scope replay)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/AEMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-local-multiplicity-one-a1-densi-4c8a5b05e0/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-local-multiplicity-one-a1-densi-4c8a5b05e0/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/dema-split-k7q2/src/T0.lean`
- `/tmp/dema-split-k7q2/src/Full.lean`
- `/tmp/dema-split-k7q2/src/Assembly.lean`
- `/tmp/dema-split-k7q2/sub2/GMT/Ch05/Submission.lean`
- `/tmp/dema-split-k7q2/cmp/ChallengeA.lean`
- `/tmp/dema-split-k7q2/cmp/SolutionA.lean`
- `/tmp/dema-split-k7q2/cmp/ChallengeB.lean`
- `/tmp/dema-split-k7q2/cmp/SolutionB.lean`
- `/tmp/dema-split-k7q2/cmp/ChallengeP.lean`
- `/tmp/dema-split-k7q2/cmp/SolutionP.lean`

Pinned snapshot (manifest.json): project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d.

The snapshot Contract.lean and Submission.lean are byte-identical to the workspace copies. Submission equals Contract, with only main_theorem sorry, so there is no prior proof to reuse. 'dohr_lmo_dema' matches nothing in the snapshot project, GMT/, simongmt or dag.json, so both proposed names are free. No DAG node states a withDensity, rnDeriv or local-finiteness lemma of this form. Sibling dohr_lmo_weight_restrict_eq is a different statement that requires theta = 1.

Mathlib support, at snapshot line numbers:
- Besicovitch.ae_tendsto_rnDeriv (Besicovitch.lean:1078); instHasBesicovitchCovering (BesicovitchVectorSpace.lean:499); sigmaFinite_of_locallyFinite (SFinite.lean:709).
- Measure.rnDeriv_withDensity₀ (Lebesgue.lean:584); measure_compl_support and isClosed_support (Support.lean:202, 115).
- lintegral_indicator₀ (Lebesgue/Basic.lean:518); Measure.restrict_restrict₀, ae_restrict_iff' and ae_restrict_mem₀ (Restrict.lean:198, 629, 637); aemeasurable_indicator_iff₀ (AEMeasurable.lean:323).
- measure_closedBall_lt_top (Typeclasses/Finite.lean:364); ENNReal.Tendsto.mul (ENNReal/Lemmas.lean:337); withDensity_absolutelyContinuous (WithDensity.lean:146); Real.ofReal_le_enorm (Normed/Group/Real.lean:118).
- Differentiation.lean gives the general Vitali-family version but no ready-made gauge-relative density lemma, so child 1 is a new obligation.

Comparator scope, replayed with gmt-compare.py contract_scope: open MeasureTheory Metric Set Filter Topology; open scoped ENNReal NNReal; namespace GMT.Ch05; namespace/end RectifiableVarifold; open RectifiableVarifold. All three types pass validate_lean_statement.

Lean checks:
- Full.lean proves both children completely and then the parent's exact frozen type from them. #print axioms gives propext, Classical.choice and Quot.sound only.
- Assembly.lean proves the parent from sorry-stubbed children.
- The comparator-style Challenge/Solution files for A, B and P elaborate. Each Solution closes by exact Submission.X with standard axioms only.
