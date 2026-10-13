# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.integral_density-a1`
- Child DAG node: `root.integral_compactness-a1.integral_density-a1.restrict_sigma_finite-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof (the multiplicity θ of v(M,θ) is positive on M and locally integrable, Simon Ch. 8 p. 206 / Remark 5.9), stated for an arbitrary measure μ on ℝ^N = Euclidean N; the parent applies it with μ = H^n = μHE[n]. Notation: μ⌞E := μ.restrict E; B̄_q(c) := closedBall c q.

1. Restrictions to arbitrary (possibly non-measurable) sets E: (i) (μ⌞E)(B) = μ(B ∩ E) for every Borel B (Measure.restrict_apply); (ii) μ(t ∩ E) ≤ (μ⌞E)(t) for every set t (Measure.le_restrict_apply).

2. Countable compact cover of U. ℝ^N is separable; fix a countable dense D ⊆ ℝ^N (TopologicalSpace.exists_countable_dense). Let 𝒦 be the countable family of closed balls B̄_q(c) with c ∈ D, q ∈ ℚ, q > 0 and B̄_q(c) ⊆ U. Each K ∈ 𝒦 is compact (ℝ^N is proper) and K ⊆ U. Moreover U = ⋃𝒦: for y ∈ U choose ε > 0 with B̄_ε(y) ⊆ U (U open), a rational q with 0 < q < ε/2 and c ∈ D with |c − y| < q; then y ∈ B̄_q(c) ⊆ B̄_{2q}(y) ⊆ B̄_ε(y) ⊆ U, so B̄_q(c) ∈ 𝒦.

3. Borel representatives. Fix K ∈ 𝒦 and put μ_K := μ⌞(M ∩ K). By hypothesis θ is μ_K-integrable, hence μ_K-a.e. strongly measurable: there is a Borel g_K : ℝ^N → ℝ with μ_K(E_K) = 0, where E_K := {y : θ(y) ≠ g_K(y)}. Since the integrands agree μ_K-a.e., ∫⁻ ofReal(g_K) dμ_K = ∫⁻ ofReal(θ) dμ_K < ∞ (Integrable.lintegral_lt_top).

4. A countable Borel cover of ℝ^N. Let 𝒮 consist of the closed set Uᶜ, the sets Z_K := K ∩ {g_K ≤ 0} (K ∈ 𝒦) and S_{K,k} := K ∩ {g_K ≥ 1/(k+1)} (K ∈ 𝒦, k ∈ ℕ). 𝒮 is countable and ⋃𝒮 = ℝ^N: a point y ∉ U lies in Uᶜ; a point y ∈ U lies in some K ∈ 𝒦 (step 2), and then either g_K(y) ≤ 0 (so y ∈ Z_K) or g_K(y) > 0, whence g_K(y) ≥ 1/(k+1) for some k ∈ ℕ (so y ∈ S_{K,k}).

5. Each member of 𝒮 has finite μ⌞M-measure.
 (a) (μ⌞M)(Uᶜ) = μ(Uᶜ ∩ M) = μ(∅) = 0, because M ⊆ U.
 (b) (μ⌞M)(Z_K) = μ(Z_K ∩ M) by 1(i). If y ∈ Z_K ∩ M then θ(y) > 0 ≥ g_K(y), so y ∈ E_K ∩ (M ∩ K). By 1(ii) and step 3, μ(Z_K ∩ M) ≤ μ(E_K ∩ (M ∩ K)) ≤ μ_K(E_K) = 0.
 (c) Let c_k := 1/(k+1) > 0 and L_k := {y : g_K(y) ≥ c_k}, a Borel set. By 1(i), (μ⌞M)(S_{K,k}) = μ(K ∩ L_k ∩ M) = μ(L_k ∩ (M ∩ K)) = μ_K(L_k). Since c_k > 0, L_k = {y : ofReal(c_k) ≤ ofReal(g_K(y))}, so Markov's inequality for the measurable function ofReal∘g_K (mul_meas_ge_le_lintegral₀) gives ofReal(c_k)·μ_K(L_k) ≤ ∫⁻ ofReal(g_K) dμ_K < ∞, i.e. (μ⌞M)(S_{K,k}) ≤ (k+1)·∫⁻ ofReal(θ) dμ_K < ∞.

6. Since ℝ^N is covered by the countably many sets in 𝒮, each of finite μ⌞M-measure, μ⌞M is σ-finite (Measure.sigmaFinite_of_countable). ∎

## Key steps

1. Restriction facts for arbitrary sets: (μ⌞E)(B) = μ(B∩E) for Borel B and μ(t∩E) ≤ (μ⌞E)(t).
2. U is the union of the countable family 𝒦 of closed balls with dense-set centres and rational radii contained in U.
3. For K ∈ 𝒦 pick a Borel g_K equal to θ μ⌞(M∩K)-a.e., with ∫⁻ ofReal g_K d(μ⌞(M∩K)) < ∞.
4. Uᶜ, Z_K = K ∩ {g_K ≤ 0} and S_{K,k} = K ∩ {g_K ≥ 1/(k+1)} form a countable cover of ℝ^N.
5. (μ⌞M)(Uᶜ) = 0 since M ⊆ U; (μ⌞M)(Z_K) = 0 since θ > 0 on M; (μ⌞M)(S_{K,k}) < ∞ by Markov.
6. Measure.sigmaFinite_of_countable gives σ-finiteness of μ⌞M.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git -C snapshot/mathlib log -1 -> 25730c7c`
- `sha256sum snapshot project/GMT/Ch08/Contract.lean, workspace GMT/Ch08/Contract.lean, GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `grep -n 'structure Varifold|def weight|theorem weight_apply|instSigmaFinite' simongmt Chapter08/Varifold.lean`
- `grep -n 'def HasWeightedApproximateTangentSpaceAt|def blowUpMap|def CountablyRectifiable' simongmt Chapter03/Rectifiable.lean`
- `grep -rn 'theorem simon_theorem_3_6|measurable_dimensionalUpperDensity|measurable_dimensionalLowerDensity|measure_toOuterMeasure_isBorelRegular|IsCaratheodoryMeasurable|nhdsGT_zero_basis_rat|volume_closedBall_eq_densityNormalization|def IsOpenSigmaFinite' simongmt Chapter01`
- `grep -rn 'def realUnitBallVolume|simonHausdorffMeasureReal_toOuterMeasure|simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure|realUnitBallVolume_nat_eq' simongmt`
- `rg -n 'hausdorffMeasure_smul₀|euclideanHausdorffMeasure_homothety_image|Isometry.euclideanHausdorffMeasure_image|euclideanHausdorffMeasure_eq_volume|hausdorffMeasure_zero_singleton' snapshot mathlib/Mathlib`
- `rg -n 'measurable_measure_prodMk_left|restrict_toMeasurable_of_sFinite|measure_toMeasurable_inter_of_sFinite|restrict_restrict_of_subset|le_restrict_apply|restrict_withDensity|restrict_add_restrict_compl|sigmaFinite_of_countable|withDensity_apply|mul_meas_ge_le_lintegral₀|integral_map_equiv|integral_smul_measure|integral_eq_lintegral_of_nonneg_ae|ae_restrict_mem₀|tendsto_of_liminf_eq_limsup|HasBasis.limsup_eq_iInf_iSup|HasBasis.liminf_eq_iSup_iInf|Integrable.lintegral_lt_top|addHaar_closedBall_eq_addHaar_ball|EuclideanSpace.volume_ball|InnerProductSpace.volume_closedBall|exists_countable_dense' snapshot mathlib/Mathlib`
- `python3 -I gmt-compare.py contract_scope(Contract.lean, GMT.Ch08.main_theorem) -> replay: open Set Filter MeasureTheory Metric; open scoped Topology ENNReal CompactlySupported Pointwise; namespace GMT.Ch08; open Poincare.SimonGMT; open Poincare.SimonGMT.Chapter08; section Definitions; end Definitions`
- `python3 -I verifier/lean_contract.py validate_lean_statement on the 5 child lean_statements`
- `lake env lean /tmp/intdens-decomp/Challenge.lean (5 statements in exact comparator challenge form)`
- `lake env lean /tmp/intdens-decomp/Assembly.lean (5 sorried Submission.* stubs + sorry-free proof of Submission.intcpt_integral_density_integer at the frozen type)`
- `lake env lean /tmp/intdens-decomp/Axioms.lean (#check / #print axioms for the cited SimonGMT and Mathlib lemmas)`
- `lake env lean /tmp/intdens-decomp/PP.lean (pp.parens print of elaborated child types)`
- `grep -rl 'intcpt_id_' run directory (dag.json, DAG.md, nodes/*) -> 0 hits; dag.json lean_name/status listing for reuse check`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/EuclideanHausdorffUpper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-integral-density-a1/parent-child-handoff.json`
- `/tmp/intdens-decomp/Challenge.lean`
- `/tmp/intdens-decomp/Assembly.lean`
- `/tmp/intdens-decomp/Axioms.lean`
- `/tmp/intdens-decomp/PP.lean`

Snapshot = project 63436ae6 + Mathlib 25730c7c; the snapshot Contract is byte-identical to the workspace Contract and Submission. Mathlib has no varifold theory, so the Ch. 8 objects come from the frozen contract and the pinned SimonGMT package.

SimonGMT facts used:
- Chapter01.simon_theorem_3_6: upper density theorem for a Borel-regular outer measure and a Carathéodory-measurable set of finite measure.
- Chapter01.measure_toOuterMeasure_isBorelRegular.
- Chapter01.simonHausdorffMeasureReal_toOuterMeasure with Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure: Simon's H^n equals μHE[n].
- Chapter01.volume_closedBall_eq_densityNormalization: realUnitBallVolume n equals the contract's ω_n, including n = 0.
- Chapter08.Varifold.weight_apply and the instance SigmaFinite V.weight.
- Chapter03.HasWeightedApproximateTangentSpaceAt: Bochner integrals over blowUpMap x r '' M.

SimonGMT's measurable_dimensional{Upper,Lower}Density require every closed ball to have finite mass, which μ_V may violate near ∂U. measurable_densities therefore uses Mathlib's measurable_measure_prodMk_left for s-finite measures instead.

Mathlib supplies:
- Hausdorff homothety and isometry scaling: euclideanHausdorffMeasure_homothety_image, Isometry.euclideanHausdorffMeasure_image, InnerProductSpace.euclideanHausdorffMeasure_eq_volume.
- s-finite measurable hulls: restrict_toMeasurable_of_sFinite, restrict_restrict_of_subset.
- The withDensity/restrict API, Markov's inequality (mul_meas_ge_le_lintegral₀) and sigmaFinite_of_countable.
- limsup/liminf basis formulas and tendsto_of_liminf_eq_limsup.

All cited SimonGMT lemmas use only propext, Classical.choice and Quot.sound. Three of their modules are not yet imported by Submission (Chapter01.DensityComparison, Chapter01.Densities, Chapter02.AreaLiteral); adding them is allowed because only Submission.lean may differ from the frozen commit.

The 5 child statements elaborate in the exact comparator form, and the parent assembly built from them type-checks with no sorry of its own. The intcpt_id_* names are unreserved, and no accepted DAG declaration has an identical type, so nothing is reused.
