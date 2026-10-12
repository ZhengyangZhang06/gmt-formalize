# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.integral_density-a1`
- Child DAG node: `root.integral_compactness-a1.integral_density-a1.zero_density_off_set-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof (Simon Ch. 1, Theorem 3.6, localized as in Remark 3.7(2)). The SimonGMT lemmas used live in Poincare.SimonGMT.Chapter01.DensityComparison, Chapter01.Densities and Chapter02.AreaLiteral (to be imported by the implementation; they use only propext, Classical.choice, Quot.sound). Notation: H^n := μHE[n]; ω_n := unitBallVolume n; B̄_s(z) := closedBall z s; for an outer measure ξ on ℝ^N and a set A, Θ*(ξ,A,y) := Chapter01.dimensionalUpperDensity ξ n A y = limsup_{ρ↓0} ξ(A ∩ B̄_ρ(y))/(realUnitBallVolume n · ofReal(ρ)^(n:ℝ)).

1. Countable cover of U by good balls. Fix a countable dense D ⊆ ℝ^N and let F := {(c,q) ∈ D × ℚ : q > 0, B̄_{2q}(c) ⊆ U}, a countable set. For y ∈ U choose ε > 0 with B̄_ε(y) ⊆ U, a rational q ∈ (0, ε/3) and c ∈ D with |c − y| < q; then y ∈ B̄_q(c) and B̄_{2q}(c) ⊆ B̄_{3q}(y) ⊆ U. Hence U ⊆ ⋃_{(c,q)∈F} B̄_q(c).

2. Upper density theorem on one ball. Fix (c,q) ∈ F and let μ_{cq} := μ⌞B̄_{2q}(c); it is a finite measure since B̄_{2q}(c) is a compact subset of U. Its outer measure is Borel regular (Chapter01.measure_toOuterMeasure_isBorelRegular); A is Borel, hence Carathéodory measurable for it (MeasureTheory.le_toOuterMeasure_caratheodory); and μ_{cq}(A) ≤ μ(B̄_{2q}(c)) < ∞. Chapter01.simon_theorem_3_6 (real dimension n ≥ 0) yields simonHausdorffOuterMeasureReal n (E_{cq}) = 0 for E_{cq} := {y : y ∉ A ∧ Θ*(μ_{cq},A,y) ≠ 0}. Since simonHausdorffOuterMeasureReal n = (simonHausdorffMeasureReal n).toOuterMeasure (Chapter01.simonHausdorffMeasureReal_toOuterMeasure) and simonHausdorffMeasureReal n = μHE[n] (Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure), H^n(E_{cq}) = 0.

3. Identification of the quotients. realUnitBallVolume n = ω_n: by Chapter01.volume_closedBall_eq_densityNormalization with r = 1 the closed unit ball of ℝ^n = EuclideanSpace ℝ (Fin n) has volume realUnitBallVolume n, and it has the same volume as the open unit ball (Measure.addHaar_closedBall_eq_addHaar_ball for n ≥ 1; for n = 0 both balls are the one-point space). Also ofReal(ρ)^(n:ℝ) = ofReal(ρ)^n (ENNReal.rpow_natCast). Let y ∈ B̄_q(c) and 0 < ρ ≤ q. Then B̄_ρ(y) ⊆ B̄_{2q}(c), so μ_{cq}(A ∩ B̄_ρ(y)) = μ(A ∩ B̄_ρ(y)) = (μ⌞A)(B̄_ρ(y)) (restrict_apply, closed balls being Borel). Hence the quotient defining Θ*(μ_{cq},A,y) equals densityRatio n (μ⌞A) y ρ for all ρ ∈ (0,q], and therefore limsup_{ρ↓0} densityRatio n (μ⌞A) y ρ = Θ*(μ_{cq},A,y) (Filter.limsup_congr).

4. Conclusion. Let y ∈ U with y ∉ A and suppose HasDensity n (μ⌞A) y 0 fails. Choose (c,q) ∈ F with y ∈ B̄_q(c) (step 1). If Θ*(μ_{cq},A,y) = 0, then by step 3 the nonnegative function ρ ↦ densityRatio n (μ⌞A) y ρ has limsup 0 along 𝓝[>]0, hence also liminf 0, so it tends to 0 (tendsto_of_liminf_eq_limsup) — a contradiction. Thus y ∈ E_{cq}. The exceptional set {y : y ∈ U ∧ y ∉ A ∧ ¬HasDensity n (μ⌞A) y 0} is therefore contained in the countable union ⋃_{(c,q)∈F} E_{cq} of H^n-null sets, so it is H^n-null, which is the asserted a.e. statement. ∎

## Key steps

1. Cover U by countably many balls B̄_q(c) with B̄_{2q}(c) ⊆ U.
2. On each ball apply Simon 1.3.6 (Chapter01.simon_theorem_3_6) to the finite Borel-regular measure μ⌞B̄_{2q}(c) and the Borel set A; convert Simon's Hausdorff outer measure to μHE[n].
3. For y ∈ B̄_q(c) and ρ ≤ q, Simon's density quotient equals densityRatio n (μ⌞A) y ρ (same normalization ω_n, ρ^n).
4. Zero upper density forces the ratio to tend to 0; the exceptional set lies in a countable union of H^n-null sets.

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
