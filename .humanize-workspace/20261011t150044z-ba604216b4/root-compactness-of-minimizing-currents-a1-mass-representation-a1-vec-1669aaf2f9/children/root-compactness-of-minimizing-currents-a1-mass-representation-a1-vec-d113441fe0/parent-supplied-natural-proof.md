# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.vector_riesz-a1.common_density-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.vector_riesz-a1.common_density-a1.density_representation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3, 5, 6 and 7 of the parent's supplied proof. They are already written for a single measure ξ ∈ {aᵢ, bᵢ} with ξ ≪ μ₀. Here μ₀ and ξ are arbitrary compact-finite measures with ξ ≪ μ₀. The parent applies the lemma 2m times, with ξ = aᵢ and ξ = bᵢ for each i ∈ Fin m.
Hypotheses:
- X is a locally compact Hausdorff space with a countable basis and its Borel σ-algebra. The Hausdorff hypothesis is not used below.
- μ₀ and ξ are measures on X, both finite on compact sets, with ξ ≪ μ₀.

1. (σ-finiteness and Lebesgue decomposition.)
 - X is locally compact with a countable basis, so it is σ-compact (sigmaCompactSpace_of_locallyCompact_secondCountable).
 - On a σ-compact space every measure that is finite on compact sets is σ-finite (SigmaFinite.of_isFiniteMeasureOnCompacts): X is the union of the countably many compact sets compactCovering X n, each of finite measure. So μ₀ and ξ are σ-finite.
 - In particular ξ is s-finite and μ₀ is σ-finite, so the pair (ξ, μ₀) has a Lebesgue decomposition (instance Measure.haveLebesgueDecomposition_of_sigmaFinite).
2. (The density δ.) Let δ := ξ.rnDeriv μ₀ : X → [0, ∞].
 - δ is measurable (Measure.measurable_rnDeriv).
 - The Lebesgue decomposition from step 1 gives ξ = ξ.singularPart μ₀ + μ₀.withDensity δ (Measure.haveLebesgueDecomposition_add).
 - Since ξ ≪ μ₀, the singular part vanishes: ξ.singularPart μ₀ = 0 (Measure.singularPart_eq_zero_of_ac). Hence ξ = μ₀.withDensity δ.
 - Since ξ is σ-finite, δ(x) < ∞ for μ₀-almost every x (Measure.rnDeriv_lt_top).
3. (Definition and measurability of g.) Define g : X → ℝ by g(x) := (δ x).toReal. g is measurable, as the composition of the measurable δ with the measurable map ENNReal.toReal (Measurable.ennreal_toReal).
4. (g is μ₀-integrable on every compact set.) Let K ⊆ X be compact.
 - ξ(K) < ∞, since ξ is finite on compact sets.
 - Measure.lintegral_rnDeriv_lt_top_of_measure_ne_top, applied with s = K (no measurability of K is required), gives ∫⁻_{x ∈ K} δ(x) dμ₀(x) < ∞.
 - δ is measurable, hence a.e.-measurable for μ₀ restricted to K.
 - integrable_toReal_of_lintegral_ne_top then shows that x ↦ (δ x).toReal = g(x) is integrable for μ₀ restricted to K, i.e. IntegrableOn g K μ₀.
5. (f·g is μ₀-integrable for f ∈ C_c(X, ℝ).) Let f ∈ C_c(X, ℝ).
 (i) f is continuous and X carries its Borel σ-algebra, so f is measurable (Continuous.measurable). In particular f is a.e.-strongly measurable for every measure.
 (ii) f has compact support, so K_f := tsupport f is compact. A continuous function with compact support is bounded: there is C ∈ ℝ with ‖f(x)‖ = |f(x)| ≤ C for all x ∈ X (Continuous.bounded_above_of_compact_support).
 (iii) By step 4, g is integrable for μ₀ restricted to K_f. Integrable.bdd_mul says that multiplying an integrable function by a bounded, a.e.-strongly measurable factor keeps it integrable. Apply it with factor f and the bound C, which holds everywhere and hence a.e. So x ↦ f(x)·g(x) is μ₀-integrable on K_f.
 (iv) For x ∉ K_f, f(x) = 0 (image_eq_zero_of_notMem_tsupport), hence f(x)·g(x) = 0. A function that is integrable on a set and vanishes at every point outside it is integrable (IntegrableOn.integrable_of_forall_notMem_eq_zero). So x ↦ f(x)·g(x) is μ₀-integrable.
6. (The integral identity.) Let f ∈ C_c(X, ℝ).
 - By step 2, ∫ f dξ = ∫ f d(μ₀.withDensity δ).
 - δ is measurable and δ < ∞ μ₀-a.e. (step 2), so integral_withDensity_eq_integral_toReal_smul gives ∫ f d(μ₀.withDensity δ) = ∫ (δ x).toReal • f(x) dμ₀(x) = ∫ g(x)·f(x) dμ₀(x).
 - Real multiplication is commutative, so g(x)·f(x) = f(x)·g(x) pointwise. Hence ∫ f dξ = ∫ f(x)·g(x) dμ₀(x).
7. By steps 3–6:
 - g is measurable and μ₀-integrable on every compact subset of X;
 - for every f ∈ C_c(X, ℝ), x ↦ f(x)·g(x) is μ₀-integrable and ∫ f dξ = ∫ f(x)·g(x) dμ₀(x).
 This proves the claim.

## Key steps

1. X is σ-compact, so the compact-finite measures μ₀ and ξ are σ-finite and (ξ, μ₀) has a Lebesgue decomposition.
2. δ := ξ.rnDeriv μ₀ is measurable. Since ξ ≪ μ₀, the singular part vanishes (singularPart_eq_zero_of_ac), so ξ = μ₀.withDensity δ; also δ < ∞ μ₀-a.e. (rnDeriv_lt_top).
3. g := (δ ·).toReal is measurable. For compact K, ξ(K) < ∞ gives ∫⁻_K δ dμ₀ < ∞, so g is integrable on K (integrable_toReal_of_lintegral_ne_top).
4. For f ∈ C_c(X, ℝ): f is measurable and bounded with compact tsupport, so f·g is integrable on tsupport f (Integrable.bdd_mul) and vanishes outside it, hence is μ₀-integrable.
5. integral_withDensity_eq_integral_toReal_smul gives ∫ f dξ = ∫ (δ x).toReal • f x dμ₀ = ∫ f x · g x dμ₀.

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
