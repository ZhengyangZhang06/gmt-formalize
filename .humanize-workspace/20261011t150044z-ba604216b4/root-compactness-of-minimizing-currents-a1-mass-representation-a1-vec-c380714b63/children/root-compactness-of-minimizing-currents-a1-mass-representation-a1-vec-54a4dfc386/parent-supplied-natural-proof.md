# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.vector_riesz-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.vector_riesz-a1.coordinate_assembly-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 7 and 9 of the parent proof.
Notation: for v ∈ H := EuclideanSpace ℝ (Fin d), v_j is its j-th coordinate. So (e_i)_j = 1 if j = i and 0 otherwise, and ⟨v, w⟩ = Σ_j v_j·w_j (PiLp.inner_apply; the real inner product on ℝ is multiplication).
1. (Definition of ν.) ν(x) := Σ_{i ∈ Fin d} ρᵢ(x)·e_i. Then ν(x)_j = Σ_i ρᵢ(x)·(e_i)_j = ρⱼ(x) for every j.
2. (Measurability.) Each x ↦ ρᵢ(x)·e_i is measurable: a measurable real function times a fixed vector (Measurable.smul_const). A finite sum of measurable H-valued functions is measurable (Finset.measurable_sum). So ν is measurable.
3. (Integrability on compact sets.) Let K be compact. Each x ↦ ρᵢ(x)·e_i is μ₀-integrable on K, since ρᵢ is (Integrable.smul_const). Hence the finite sum ν is μ₀-integrable on K (integrable_finsetSum).
4. (Coordinates of g.) Fix g ∈ C_c(X, H).
 The coordinate map pᵢ : H → ℝ, v ↦ v_i, is continuous linear with pᵢ(0) = 0. So gᵢ := g.compLeft pᵢ ∈ C_c(X, ℝ) and gᵢ(x) = g(x)_i.
 The map cᵢ : ℝ → H, t ↦ t·e_i, is continuous with cᵢ(0) = 0. So Gᵢ := gᵢ.compLeft cᵢ ∈ C_c(X, H) and Gᵢ(x) = gᵢ(x)·e_i (CompactlySupportedContinuousMap.compLeft_apply).
5. (Decomposition of g.) g = Σ_i Gᵢ in C_c(X, H): for every x and j, (Σ_i Gᵢ(x))_j = Σ_i g(x)_i·(e_i)_j = g(x)_j. Elements of C_c(X, H) with the same values are equal; the value of a finite sum is the pointwise sum (CompactlySupportedContinuousMap.coe_sum).
6. (Applying the hypothesis.) By linearity of L and the hypothesis with f := gᵢ and g := Gᵢ (valid since Gᵢ(x) = gᵢ(x)·e_i for all x):
 L g = Σ_i L Gᵢ = Σ_i ∫ gᵢ(x)·ρᵢ(x) dμ₀(x).
7. (Integrability of gᵢρᵢ.) K := tsupport gᵢ is compact. gᵢ is continuous, hence measurable since open sets are measurable, and bounded: |gᵢ(x)| ≤ C for some C, being continuous with compact support. ρᵢ is μ₀-integrable on K, so x ↦ gᵢ(x)·ρᵢ(x) is μ₀-integrable on K (bounded measurable times integrable, Integrable.bdd_mul). It vanishes outside K, where gᵢ = 0, so it is μ₀-integrable on X (IntegrableOn.integrable_of_forall_notMem_eq_zero).
8. (Interchanging sum and integral.) By step 7, Σ_i ∫ gᵢρᵢ dμ₀ = ∫ Σ_i gᵢ(x)·ρᵢ(x) dμ₀(x) (integral_finsetSum).
9. (Inner product.) For every x, Σ_i gᵢ(x)·ρᵢ(x) = Σ_i g(x)_i·ν(x)_i = ⟨g(x), ν(x)⟩, by steps 1 and 4.
10. Combining steps 6, 8 and 9 gives L g = ∫ ⟨g(x), ν(x)⟩ dμ₀(x) for every g ∈ C_c(X, H). Together with steps 2 and 3, ν has all the required properties.

## Key steps

1. Define ν := Σᵢ ρᵢ e_i; then ν(x)_j = ρⱼ(x), and ν is measurable and integrable on compacts as a finite sum of ρᵢ·(constant vector).
2. For g ∈ C_c(X,H), the coordinates gᵢ = pᵢ ∘ g and Gᵢ = gᵢ(·)e_i lie in C_c, and g = Σᵢ Gᵢ (coordinatewise extensionality).
3. Linearity plus the hypothesis give L g = Σᵢ ∫ gᵢ ρᵢ dμ₀.
4. Each gᵢρᵢ is integrable: bounded continuous times integrable on the compact tsupport, and zero outside it.
5. Swap the finite sum and the integral, then use ⟨g(x), ν(x)⟩ = Σᵢ g(x)ᵢ ρᵢ(x).

## Reference use

### local-project

Queries:
- `rg -n 'cmr_vr|jordan_decomposition|common_density|coordinate_assembly|coordinate_functional' <snapshot>/project -g '*.lean'  (no match)`
- `rg -n -i 'jordan' <snapshot>/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/  (no match: Mathlib has no Jordan decomposition of functionals on C_c)`
- `grep -n 'def compLeft|compLeft_apply|def nnrealPart|def toReal|def toRealPositiveLinear|eq_toRealPositiveLinear_toReal|sup_apply|inf_apply|instance.*Lattice|toNNRealLinear' <snapshot>/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean`
- `rg -n 'def rieszMeasure|theorem integral_rieszMeasure|regular_rieszMeasure' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `rg -n 'measurable_rnDeriv|haveLebesgueDecomposition_add|singularPart_eq_zero_of_ac|lintegral_rnDeriv_lt_top_of_measure_ne_top|rnDeriv_lt_top' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `rg -n 'theorem withDensity_rnDeriv_eq|setLIntegral_rnDeriv' <snapshot>/mathlib/Mathlib -g '*.lean'  (found in RadonNikodym.lean, but #check after import GMT.Ch07.Submission reports unknown constant)`
- `rg -n 'integral_withDensity_eq_integral_toReal_smul|theorem Integrable.bdd_mul|theorem Integrable.mul_bdd|IntegrableOn.integrable_of_forall_notMem_eq_zero|SigmaFinite.of_isFiniteMeasureOnCompacts|sigmaCompactSpace_of_locallyCompact_secondCountable' <snapshot>/mathlib/Mathlib -g '*.lean'`
- `python3: contract_scope() from verifier/gmt-compare.py applied to GMT/Ch07/Contract.lean (scope replay for child challenges)`
- `python3 scan of dag.json lean_name for cmr_vr_* and the four proposed names (all free; 668 nodes)`
- `lake env lean /tmp/vr-split-c380/Avail.lean Avail2.lean Inst.lean (#check / #synth: rieszMeasure, toRealPositiveLinear, IsFiniteMeasureOnCompacts and SigmaFinite instances, WithLp.measurableSpace / PiLp.borelSpace on EuclideanSpace)`
- `lake env lean /tmp/vr-split-c380/Stmts.lean (4 frozen child types + parent glue) and /tmp/vr-split-c380/All.lean (complete child proofs + glue, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-vec-c380714b63/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/vr-split-c380/Stmts.lean`
- `/tmp/vr-split-c380/All.lean`
- `/tmp/vr-split-c380/C1.lean`
- `/tmp/vr-split-c380/C2.lean`
- `/tmp/vr-split-c380/C3.lean`
- `/tmp/vr-split-c380/C4.lean`

No reusable declaration exists:
- No cmr_vr_* or Jordan-decomposition-of-functionals declaration exists in the project snapshot or in Mathlib's C_c/RMK files.
- The four proposed names are free in dag.json.

In-closure Mathlib API (snapshot line numbers):
- CompactlySupported.lean: compLeft / compLeft_apply (137/150), lattice sup_apply/inf_apply (464/490), nnrealPart (688), toReal (739), toRealPositiveLinear (799), eq_toRealPositiveLinear_toReal (825).
- RieszMarkovKakutani/Real.lean: rieszMeasure (65), integral_rieszMeasure (345), regular_rieszMeasure (357), hence IsFiniteMeasureOnCompacts.
- Lebesgue.lean: measurable_rnDeriv (100), haveLebesgueDecomposition_add (115), singularPart_eq_zero_of_ac (252), lintegral_rnDeriv_lt_top_of_measure_ne_top (364), rnDeriv_lt_top (384).
- integral_withDensity_eq_integral_toReal_smul (Bochner/ContinuousLinearMap.lean:318).
- Integrable.bdd_mul / mul_bdd (Integrable.lean:1067/1072).
- IntegrableOn.integrable_of_forall_notMem_eq_zero (IntegrableOn.lean:453).
- SigmaFinite.of_isFiniteMeasureOnCompacts (SFinite.lean:701).
- sigmaCompactSpace_of_locallyCompact_secondCountable (SigmaCompact.lean:187).

Not in the import closure, so the child proofs avoid them: RadonNikodym.lean (withDensity_rnDeriv_eq, setLIntegral_rnDeriv) and EuclideanSpace.measurableEquiv.

Comparator scope: the child-comparator replay (open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (...); noncomputable section; end) was reproduced. All four child types elaborate in it.

Lean results:
- The parent glue compiles from the four child types.
- Complete Lean proofs of all four children were also checked (All.lean). Every theorem, including the assembled cmr_vector_riesz_representation, depends only on propext, Classical.choice and Quot.sound.
