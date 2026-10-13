# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.vector_riesz-a1.common_density-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.vector_riesz-a1.common_density-a1.dominating_measure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2 and 4 of the parent's supplied proof (the dominating measure μ₀ := Σᵢ (aᵢ + bᵢ) and absolute continuity), stated for arbitrary families of compact-finite measures. The parent applies it with aᵢ := RealRMK.rieszMeasure Λ₂ᵢ and bᵢ := RealRMK.rieszMeasure Λ₁ᵢ.
Hypotheses:
- X is a topological space with a σ-algebra; no compatibility is assumed or needed.
- m ∈ ℕ.
- a, b : Fin m → Measure X, with every aᵢ and every bᵢ finite on compact sets.

1. (Definition of μ₀.) Let μ₀ := Σ_{i ∈ Fin m} (aᵢ + bᵢ), the finite sum over Finset.univ of the measures aᵢ + bᵢ in the additive commutative monoid of measures on X. For m = 0 it is the zero measure. Evaluating a measure at a set commutes with sums of two measures (Measure.add_apply) and with finite sums of measures (Measure.finsetSum_apply). Both identities hold for every set s ⊆ X, measurable or not. Hence for every s ⊆ X:
 μ₀(s) = Σ_{i ∈ Fin m} (aᵢ(s) + bᵢ(s)) in [0, ∞]. (★)
2. (μ₀ is finite on compact sets.) Let K ⊆ X be compact and i ∈ Fin m.
 - aᵢ(K) < ∞ and bᵢ(K) < ∞, because aᵢ and bᵢ are finite on compact sets (IsFiniteMeasureOnCompacts.lt_top_of_isCompact).
 - Hence aᵢ(K) + bᵢ(K) < ∞ (ENNReal.add_lt_top).
 - A finite sum in [0, ∞] whose terms are all < ∞ is itself < ∞ (ENNReal.sum_lt_top). By (★), μ₀(K) < ∞.
 Since K was arbitrary, μ₀ is finite on compact sets.
3. (aᵢ ≪ μ₀ and bᵢ ≪ μ₀.) Fix i ∈ Fin m and a set s ⊆ X with μ₀(s) = 0.
 - By (★), Σ_{j ∈ Fin m} (aⱼ(s) + bⱼ(s)) = 0.
 - [0, ∞] is a canonically ordered additive monoid, so a finite sum is 0 iff each term is 0 (Finset.sum_eq_zero_iff). Taking j = i ∈ Finset.univ gives aᵢ(s) + bᵢ(s) = 0.
 - By the same principle for two summands (add_eq_zero), aᵢ(s) = 0 and bᵢ(s) = 0.
 In Mathlib, aᵢ ≪ μ₀ means every set of μ₀-measure 0 has aᵢ-measure 0. Since s was an arbitrary μ₀-null set, aᵢ ≪ μ₀ and bᵢ ≪ μ₀.
4. By steps 2 and 3, μ₀ is finite on compact sets and aᵢ ≪ μ₀, bᵢ ≪ μ₀ for every i ∈ Fin m. This proves the claim.

## Key steps

1. Define μ₀ := Σ_{i ∈ Fin m} (aᵢ + bᵢ). By Measure.finsetSum_apply and Measure.add_apply, μ₀(s) = Σᵢ (aᵢ(s) + bᵢ(s)) for every set s.
2. For compact K each aᵢ(K) and bᵢ(K) is finite, so μ₀(K) is a finite sum of finite terms and is finite (ENNReal.add_lt_top, ENNReal.sum_lt_top).
3. If μ₀(s) = 0, every summand vanishes (Finset.sum_eq_zero_iff, add_eq_zero), so aᵢ(s) = bᵢ(s) = 0. Hence aᵢ ≪ μ₀ and bᵢ ≪ μ₀.

## Reference use

### local-project

Queries:
- `rg -n 'theorem lintegral_rnDeriv_lt_top_of_measure_ne_top|theorem setLIntegral_rnDeriv_le|theorem rnDeriv_lt_top|theorem haveLebesgueDecomposition_add|theorem singularPart_eq_zero_of_ac|theorem measurable_rnDeriv|instance.*haveLebesgueDecomposition_of_sigmaFinite|theorem withDensity_rnDeriv_eq|lemma setLIntegral_rnDeriv_le' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/`
- `rg -n 'singularPart_eq_zero_of_ac|theorem integral_withDensity_eq_integral_toReal_smul|theorem integrable_toReal_of_lintegral_ne_top|theorem Integrable.mul_bdd|theorem Integrable.bdd_mul|integrable_of_forall_notMem_eq_zero|of_isFiniteMeasureOnCompacts|sigmaCompactSpace_of_locallyCompact_secondCountable|class Regular|theorem integral_rieszMeasure|regular_rieszMeasure|def rieszMeasure' <snapshot>/mathlib/Mathlib -g '*.lean'`
- `grep -n 'BorelSpace|^variable|^section|^end' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `rg -n 'IsFiniteMeasureOnCompacts' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean; rg -n 'IsFiniteMeasureOnCompacts \(.*\+' <snapshot>/mathlib/Mathlib (no match: no instance for sums of measures)`
- `rg -n 'theorem finsetSum_apply|theorem coe_finsetSum' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Module.lean; rg -n 'absolutelyContinuous_of_le' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean`
- `rg -n 'sum_lt_top|bounded_above_of_compact_support|image_eq_zero_of_notMem_tsupport|theorem Measurable.ennreal_toReal|theorem integral_sub ' <snapshot>/mathlib/Mathlib -g '*.lean'`
- `sed -n 440,485p <snapshot>/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean (LocallyIntegrable.integrable_smul_left_of_hasCompactSupport, alternative route)`
- `rg -n 'cmr_vr|dominating_measure|density_representation' <snapshot>/project -g '*.lean' (no match)`
- `python3 scan of dag.json lean_name (817 nodes, no duplicates, no cmr_vr_cd_*); grep 'cmr_vr_cd_' in dag.json, nodes/*/*.json and 3449 worktree GMT/Ch07/Submission.lean files (no match)`
- `python3 -I: contract_scope() from verifier/gmt-compare.py on GMT/Ch07/Contract.lean; cmp with <snapshot>/project/GMT/Ch07/Contract.lean (identical)`
- `lake env lean /tmp/cd-split-1669/Stmts.lean (child types + parent glue), All.lean and Final.lean (full child proofs + assembled parent + comparator-shaped targets, #print axioms), Closure.lean (#check of RadonNikodym/Lebesgue lemmas)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Module.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/BigOperators.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-vec-1669aaf2f9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/cd-split-1669/Stmts.lean`
- `/tmp/cd-split-1669/All.lean`
- `/tmp/cd-split-1669/Final.lean`
- `/tmp/cd-split-1669/Closure.lean`

No reusable declaration exists:
- The project snapshot (project b4d606db, mathlib 25730c7c) has no cmr_vr_*, dominating-measure or density-representation declaration.
- Mathlib has no IsFiniteMeasureOnCompacts instance for sums of measures, so dominating_measure is proved directly through Measure.finsetSum_apply (Module.lean:160).
- The proposed names cmr_vr_cd_dominating_measure and cmr_vr_cd_density_representation are free in dag.json, the node handoffs and the worktree Submission files.

In-closure API used by the child proofs (snapshot line numbers):
- Lebesgue.lean: measurable_rnDeriv (100), haveLebesgueDecomposition_add (115), singularPart_eq_zero_of_ac (252), lintegral_rnDeriv_lt_top_of_measure_ne_top (364), rnDeriv_lt_top (384), instance haveLebesgueDecomposition_of_sigmaFinite [SFinite μ] [SigmaFinite ν] (952).
- RieszMarkovKakutani/Real.lean: rieszMeasure (65), integral_rieszMeasure (345), regular_rieszMeasure (357). Regular extends IsFiniteMeasureOnCompacts (Regular.lean:317).
- Bochner/ContinuousLinearMap.lean: integral_withDensity_eq_integral_toReal_smul (318).
- L1Space/Integrable.lean: integrable_toReal_of_lintegral_ne_top (925), Integrable.bdd_mul (1067).
- IntegrableOn.lean: IntegrableOn.integrable_of_forall_notMem_eq_zero (453).
- SFinite.lean: SigmaFinite.of_isFiniteMeasureOnCompacts (701).
- SigmaCompact.lean: sigmaCompactSpace_of_locallyCompact_secondCountable (187).
- Basic/ENNReal/BigOperators.lean: ENNReal.sum_lt_top (101).

RadonNikodym.lean's withDensity_rnDeriv_eq and setLIntegral_rnDeriv_le are NOT in the import closure of GMT.Ch07.Submission (#check reports unknown constant), so the child proofs avoid them.

Comparator scope: contract_scope() replays
- open Filter Function Set MeasureTheory Metric
- open scoped ENNReal Topology
- namespace GMT.Ch07
- the two open Poincare.SimonGMT lines
- noncomputable section, then end

The workspace Contract.lean is byte-identical to the snapshot copy.

Lean results:
- Both frozen child types elaborate in that scope.
- The parent glue compiles from them.
- Full child proofs, the selected theorem assembled from them, and the comparator-shaped targets all compile with axioms [propext, Classical.choice, Quot.sound] only.
