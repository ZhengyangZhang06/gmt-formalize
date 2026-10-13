# Parent-supplied natural-language proof

- Parent DAG node: `root.plane_disintegration-a1`
- Child DAG node: `root.plane_disintegration-a1.pointwise_measure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 8, proof of Lemma 1.3 (pp. 207–208), first part: the countable dense family, printed (1), (3), (4) and the Riesz step. It follows steps 1–4 of the parent proof. The differentiation (1) is the sibling slice_density; the passage through (3), (4) and Riesz is the sibling riesz_limit.

Notation. G := G(N,n), μ := μ_V = V.weight, and ‖f‖ := sup_G |f| for f ∈ C(G,ℝ). For x ∈ ℝ^N, ρ ∈ ℝ and β ∈ C(G,ℝ) let
 avg_ρ^x(β) := (∫_{B_ρ(x)×G} β(z.2) dV(z)) / μ(B_ρ(x)).toReal,
 which is exactly the quotient in the statement.

1. Countable dense family (printed "β_1, β_2, … ∈ 𝒦⁺ dense in 𝒦⁺"). G is compact and second countable, so C(G,ℝ) (compact-open = sup-norm topology) is second countable, hence separable (Mathlib ContinuousMap.instSeparableSpace, Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean:108). That pure-Mathlib module is not in the contract's import closure and must be imported. Choose f_1, f_2, … with dense range in C(G,ℝ) (TopologicalSpace.exists_dense_seq).
 Put c_j := ‖f_j‖ and β_j := f_j + c_j, adding the constant function c_j. Then β_j ∈ C(G,ℝ) and β_j ≥ 0, since f_j(S) ≥ −|f_j(S)| ≥ −‖f_j‖. This is the printed passage between 𝒦⁺ and 𝒦 via β = (β + c) − c, applied to a dense sequence of 𝒦.

2. Differentiation (printed (1)). For each j, the sibling lemma slice_density applied to V and β_j ≥ 0 gives e_j : ℝ^N → ℝ such that avg_ρ^x(β_j) → e_j(x) as ρ ↓ 0 for μ-a.e. x.

3. A common conull set (the printed x ∈ ℝ^{n+ℓ} ∖ ⋃_j Z_j). Each condition below holds for μ-a.e. x. There are countably many of them, so they hold simultaneously for μ-a.e. x (ae_all_iff, filter_upwards).
(a) x ∈ U, because μ(ℝ^N∖U) = V((ℝ^N∖U) × G) = 0 (Varifold.weight_apply, V.supported).
(b) x ∈ spt μ, i.e. μ(W) > 0 for every neighbourhood W of x. ℝ^N is second countable, hence hereditarily Lindelöf, so μ(ℝ^N ∖ spt μ) = 0 (Measure.support_mem_ae, Support.lean:198; Measure.mem_support_iff_forall, :75).
(c) For every j, avg_ρ^x(β_j) → e_j(x) as ρ ↓ 0 (step 2).
 Fix such an x; it remains to produce η for it.

4. Small balls. U is open and x ∈ U, so choose r > 0 with ball(x,r) ⊆ U. For 0 < ρ < r, B_ρ(x) ⊆ ball(x,r) ⊆ U is compact, so μ(B_ρ(x)) < ∞ (Varifold.weight_finite_on_compact). Also μ(B_ρ(x)) ≥ μ(ball(x,ρ)) > 0 by (b), because the open ball ball(x,ρ) is a neighbourhood of x.

5. Slice measures. For ρ ∈ ℝ define the Borel measure on G
 m_ρ := μ(B_ρ(x))⁻¹ · σ_#(V⌞(B_ρ(x) × G)), with σ(y,S) := S,
 i.e. m ρ = (V.weight (closedBall x ρ))⁻¹ • (V.measure.restrict (closedBall x ρ ×ˢ univ)).map Prod.snd.
(a) For every ρ and every f ∈ C(G,ℝ), ∫ f dm_ρ = avg_ρ^x(f). The ingredients are:
 - ∫ f d(t·ν) = t.toReal·∫ f dν for t ∈ [0,∞] (integral_smul_measure);
 - ∫ f d(σ_#ν') = ∫ f∘σ dν', since σ is measurable and f continuous (integral_map);
 - ∫ (f∘σ) d(V⌞(B × G)) = ∫_{B×G} f(z.2) dV;
 - (μ(B)⁻¹).toReal = (μ(B).toReal)⁻¹ (ENNReal.toReal_inv).
 Together they give ∫ f dm_ρ = (μ(B).toReal)⁻¹ ∫_{B×G} f(z.2) dV = avg_ρ^x(f). This holds for every ρ; no positivity is needed.
(b) For 0 < ρ < r, m_ρ is a probability measure: m_ρ(G) = μ(B_ρ(x))⁻¹·V(B_ρ(x) × G) = μ(B_ρ(x))⁻¹·μ(B_ρ(x)) = 1, since 0 < μ(B_ρ(x)) < ∞ by step 4 (Measure.map_apply, Measure.restrict_apply, Varifold.weight_apply, ENNReal.inv_mul_cancel).

6. Limits on the dense family (printed (4) for the β_j). Let j ∈ ℕ and 0 < ρ < r. By 5(b), every f ∈ C(G,ℝ) is m_ρ-integrable and ∫ c_j dm_ρ = c_j·m_ρ(G) = c_j. Hence ∫ f_j dm_ρ = ∫ β_j dm_ρ − c_j = avg_ρ^x(β_j) − c_j (integral_add, integral_const, and 5(a) for β_j).
 Since (0, r) ∈ 𝓝[>]0 and avg_ρ^x(β_j) → e_j(x) by (c), we get ∫ f_j dm_ρ → e_j(x) − c_j as ρ ↓ 0 (Tendsto.sub_const, Tendsto.congr'). So lim_{ρ↓0} ∫ f dm_ρ exists for every f in D := {f_1, f_2, …}, which is dense in C(G,ℝ).

7. Riesz limit (printed (3), (4) and the Riesz representation). Apply the sibling lemma riesz_limit with the nontrivial filter l := 𝓝[>]0 on ℝ, the family (m_ρ), and D. Its hypotheses hold: m_ρ is a probability measure for all ρ ∈ (0, r), hence l-eventually (step 5(b)); D is dense (step 1); and limits exist on D (step 6).
 It yields a probability measure η on G with ∫ f dm_ρ → ∫ f dη as ρ ↓ 0 for every f ∈ C(G,ℝ). By 5(a), avg_ρ^x(β) = ∫ β dm_ρ for all ρ, so avg_ρ^x(β) → ∫ β dη for every continuous β : G → ℝ. Since x was an arbitrary point of the μ-conull set of step 3, the statement holds for μ-a.e. x. ∎

## Key steps

1. Take a dense sequence f_j in the separable space C(G,ℝ) and set β_j := f_j + ‖f_j‖ ≥ 0.
2. slice_density for each β_j gives avg_ρ^x(β_j) → e_j(x) μ_V-a.e.; intersect with x ∈ U and x ∈ spt μ_V (countably many conull sets).
3. For such x, 0 < μ_V(B_ρ(x)) < ∞ for small ρ. The slice measures m_ρ = μ_V(B_ρ(x))⁻¹ σ_#(V⌞(B_ρ(x)×G)) satisfy ∫ f dm_ρ = avg_ρ^x(f) for every ρ and are eventually probability measures.
4. ∫ f_j dm_ρ = avg_ρ^x(β_j) − ‖f_j‖ converges for every j.
5. riesz_limit gives a probability measure η with ∫ f dm_ρ → ∫ f dη for all f, i.e. avg_ρ^x(β) → ∫ β dη.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum project/GMT/Ch08/Contract.lean vs workspace GMT/Ch08/Contract.lean and Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'theorem ae_tendsto_rnDeriv|theorem ae_tendsto_measure_inter_div|theorem ae_tendsto_lintegral_div|ae_tendsto_average' mathlib/Mathlib/MeasureTheory/Covering/`
- `rg -n 'theorem rnDeriv_restrict|rnDeriv_restrict_self|rnDeriv_restrict_right' mathlib/Mathlib`
- `rg -n 'rnDeriv_lt_top|rnDeriv_ne_top|withDensity_rnDeriv_eq|eq_rnDeriv' mathlib/Mathlib/MeasureTheory/Measure/Decomposition/*.lean`
- `rg -n '^theorem|^lemma|^noncomputable def|^instance' mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `rg -n 'SeparableSpace C\(|SecondCountableTopology C\(|instSeparableSpace' mathlib/Mathlib/Topology/ContinuousMap/`
- `rg -n 'support_mem_ae|measure_compl_support|mem_support_iff_forall' mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `rg -n -i 'disintegr|ae_tendsto_rnDeriv|rieszMeasure|exists_dense_seq' .lake/packages/simongmt/Poincare/SimonGMT/`
- `grep -n '^theorem' simongmt Chapter01/RadonNikodymTheorem.lean Chapter01/RadonNikodymDensity.lean`
- `#check / #print axioms Varifold.ae_tendsto_firstVariationDensity_of_domainMeasure and hasBesicovitchCovering_subtype after import GMT.Ch08.Submission`
- `#synth HasBesicovitchCovering/HereditarilyLindelofSpace/ProperSpace (Euclidean N); T2Space/LocallyCompactSpace/BorelSpace/CompactSpace (Grassmannian N n); SeparableSpace C(Grassmannian N n, ℝ) (fails with contract imports, succeeds with import Mathlib.Topology.ContinuousMap.SecondCountableSpace)`
- `python3 contract_scope(Contract.lean, GMT.Ch08.main_theorem) from verifier/gmt-compare.py; validate_lean_statement from verifier/lean_contract.py on the 4 child statements`
- `lake env lean /tmp/pdis_scratch/final/FromJson.lean (4 statements + generated challenge targets + parent assembly in comparator scope)`
- `lake env lean /tmp/pdis_scratch/Full.lean (sorry-free proofs of the 4 children and plane_disintegration; #print axioms)`
- `sed -n 60,170p book/chapter-08.txt (printed Lemma 1.3 and its proof)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/RadonNikodymTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/RadonNikodymDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/pdis_scratch/final/FromJson.lean`
- `/tmp/pdis_scratch/Full.lean`

The snapshot is project 63436ae6 plus Mathlib 25730c7c. Its Ch08 Contract is byte-identical to the workspace Contract and Submission.

Library results the children rely on:
- The pinned SimonGMT library already has the kernel-checked differentiation lemma Varifold.ae_tendsto_firstVariationDensity_of_domainMeasure (FirstVariationDensity.lean:60; Besicovitch on the open subspace U via hasBesicovitchCovering_subtype, :30). It is in the import closure of GMT.Ch08.Submission, and its axioms are only propext, Classical.choice and Quot.sound. It realizes printed (1) on U without compact exhaustions. Mathlib's Besicovitch.ae_tendsto_rnDeriv (Besicovitch.lean:1078) needs locally finite measures on ℝ^N, which μ_V need not be.
- Radon–Nikodym: Measure.withDensity_rnDeriv_eq (RadonNikodym.lean:60) and Measure.rnDeriv_lt_top (Lebesgue.lean:384).
- Riesz: RealRMK.rieszMeasure / integral_rieszMeasure (RMK Real.lean:345), with the IsFiniteMeasure instance for compact spaces at :445.
- Measure.support_mem_ae (Support.lean:198).
- ContinuousMap.instSeparableSpace (SecondCountableSpace.lean:108). It is not in the contract closure, so pointwise_measure must import that pure-Mathlib module.

There is no existing disintegration lemma in Mathlib or SimonGMT, so the four children are new obligations.

Verification:
- All four child lean_statements pass validate_lean_statement and elaborate in the replayed contract scope. The challenge-style `exact Submission.X` targets close, and the parent assembly checks against the frozen type.
- Complete scratch proofs of all four children and of the parent compile with standard axioms only.
