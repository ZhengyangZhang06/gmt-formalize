# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.integral_density-a1`
- Child DAG node: `root.integral_compactness-a1.integral_density-a1.tangent_point_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof (Simon Ch. 3, Remark 1.8(2)). Notation: H^n := μHE[n] on ℝ^N = Euclidean N; ω_n := unitBallVolume n, a number in (0,∞) (the volume of the unit ball of ℝ^n; ω_0 = 1), also used for its real value; B̄_s(z) := closedBall z s; η_r := Chapter03.blowUpMap x r, η_r(z) = r^{-1}(z − x); ν := (H^n⌞M).withDensity(ofReal∘θ). For Borel B, ν(B) = ∫⁻_B ofReal θ d(H^n⌞M) = ∫⁻_M 1_B(z) ofReal θ(z) dH^n(z) (withDensity_apply, Measure.restrict_restrict). The hypothesis HWATS(n,M,θ,x,P) says: finrank P = n and, for every f ∈ C_c(ℝ^N,ℝ), ∫_{η_r(M)} f(y)θ(x + ry) dH^n(y) → θ(x)·∫_P f dH^n as r ↓ 0. Since x ∈ M, θ(x) ≥ 0.

1. Change of variables. For r > 0 and every set A ⊆ ℝ^N, H^n(η_r(A)) = r^{-n}H^n(A): η_r(z) = h(z) − x with h = AffineMap.homothety x r^{-1}, translation by −x is an isometry (Isometry.euclideanHausdorffMeasure_image), and H^n(h(A)) = |r^{-1}|^n H^n(A) (MeasureTheory.euclideanHausdorffMeasure_homothety_image). Hence H^n⌞η_r(M) = r^{-n}·(η_r)_#(H^n⌞M) as measures: for Borel B, η_r^{-1}(B) is Borel and η_r(η_r^{-1}(B) ∩ M) = B ∩ η_r(M) (Set.image_preimage_inter, η_r bijective), so H^n(B ∩ η_r(M)) = r^{-n}H^n(η_r^{-1}(B) ∩ M). As η_r is a homeomorphism, hence a measurable equivalence, integral_smul_measure and integral_map_equiv give, for every F : ℝ^N → ℝ, ∫_{η_r(M)} F dH^n = r^{-n}∫_M F(η_r(z)) dH^n(z). With F(y) = f(y)θ(x + ry) and x + r·η_r(z) = z:
 (∗) ∫_{η_r(M)} f(y)θ(x+ry) dH^n(y) = r^{-n}∫_M f(η_r(z))θ(z) dH^n(z).

2. Cutoffs. Fix κ ∈ (0,1). Let f₁(y) := min{1, max{0, (1 − |y|)/(1 − κ)}} and f₂(y) := min{1, max{0, (κ^{-1} − |y|)/(κ^{-1} − 1)}}. They are continuous, [0,1]-valued and vanish outside the compact balls B̄_1(0), resp. B̄_{1/κ}(0), so f₁, f₂ ∈ C_c(ℝ^N,ℝ), and 1_{B̄_κ(0)} ≤ f₁ ≤ 1_{B̄_1(0)} ≤ f₂ ≤ 1_{B̄_{1/κ}(0)}. As |η_r(z)| = |z − x|/r, for every z and r > 0:
 1_{B̄_{κr}(x)}(z) ≤ f₁(η_r z) ≤ 1_{B̄_r(x)}(z) ≤ f₂(η_r z) ≤ 1_{B̄_{r/κ}(x)}(z).

3. Sandwich. Let 0 < r ≤ κr₀ and g_i(z) := f_i(η_r z)θ(z) (i = 1,2). By step 2, g_i vanishes outside B̄_{r/κ}(x) ⊆ B̄_{r₀}(x) and |g_i| ≤ |θ|; f_i∘η_r is continuous and bounded and θ is H^n-integrable on M ∩ B̄_{r₀}(x), so g_i is H^n-integrable on M ∩ B̄_{r₀}(x) and hence (being the indicator of B̄_{r₀}(x) times itself) on M. As M is H^n-null-measurable, H^n⌞M-a.e. point lies in M (ae_restrict_mem₀), where g_i ≥ 0 because θ ≥ 0 on M; therefore ∫_M g_i dH^n = J_i(r).toReal with J_i(r) := ∫⁻_M ofReal(f_i(η_r z))·ofReal(θ(z)) dH^n(z) (integral_eq_lintegral_of_nonneg_ae, ENNReal.ofReal_mul). Multiplying the inequalities of step 2 by ofReal θ(z) and integrating over M (lintegral_mono; no measurability is needed):
 ν(B̄_{κr}(x)) ≤ J₁(r) ≤ ν(B̄_r(x)) ≤ J₂(r) ≤ ν(B̄_{r/κ}(x)) ≤ ν(B̄_{r₀}(x)) = ∫⁻_{M∩B̄_{r₀}(x)} ofReal θ dH^n < ∞ (Integrable.lintegral_lt_top).
 Put I_i(r) := ∫_{η_r(M)} f_i(y)θ(x+ry) dH^n(y) and a(r) := r^{-n}·ν(B̄_r(x)).toReal. By (∗), I_i(r) = r^{-n}J_i(r).toReal, so I₁(r) ≤ a(r) ≤ I₂(r) for 0 < r ≤ κr₀.

4. Plane integrals. For s > 0, H^n(P ∩ B̄_s(0)) = ω_n s^n: with the restricted inner product P is an n-dimensional inner product space (finrank P = n); the inclusion P → ℝ^N is an isometry mapping the closed s-ball of P onto P ∩ B̄_s(0), so by Isometry.euclideanHausdorffMeasure_image and InnerProductSpace.euclideanHausdorffMeasure_eq_volume, H^n(P ∩ B̄_s(0)) equals the volume of the closed s-ball of P; a linear isometry equivalence P ≃ EuclideanSpace ℝ (Fin n) preserves volume, and the closed s-ball of ℝ^n has volume realUnitBallVolume n·s^n (SimonGMT Chapter01.volume_closedBall_eq_densityNormalization, valid also for n = 0) = ω_n s^n, because realUnitBallVolume n = volume(B̄_1(0)) = volume(B_1(0)) = ω_n (the unit sphere is Lebesgue-null for n ≥ 1, Measure.addHaar_closedBall_eq_addHaar_ball; for n = 0 both balls are the whole one-point space). In particular H^n(P ∩ B̄_{1/κ}(0)) < ∞, so f₁, f₂ are H^n⌞P-integrable, and integrating 1_{B̄_κ(0)} ≤ f₁ and f₂ ≤ 1_{B̄_{1/κ}(0)} over P gives
 c₁ := ∫_P f₁ dH^n ≥ ω_nκ^n and c₂ := ∫_P f₂ dH^n ≤ ω_nκ^{-n}.

5. Limits. By the hypothesis applied to f₁ and f₂, I_i(r) → θ(x)c_i as r ↓ 0. By step 3 and θ(x) ≥ 0:
 θ(x)ω_nκ^n ≤ θ(x)c₁ ≤ liminf_{r↓0} a(r) ≤ limsup_{r↓0} a(r) ≤ θ(x)c₂ ≤ θ(x)ω_nκ^{-n}.
 Since κ ∈ (0,1) is arbitrary, a(r) → θ(x)ω_n as r ↓ 0.

6. Conclusion. For 0 < r ≤ r₀, ν(B̄_r(x)) is finite and equals ofReal(a(r)·r^n), so densityRatio n ν x r = ν(B̄_r(x))/(ω_n·ofReal(r)^n) = ofReal(a(r)/ω_n), which tends to ofReal(θ(x)ω_n/ω_n) = ofReal(θ(x)) by continuity of ofReal. Thus HasDensity n ν x (ofReal θ(x)). ∎

## Key steps

1. Change of variables: H^n(η_r(A)) = r^{-n}H^n(A), hence ∫_{η_r(M)} f(y)θ(x+ry)dH^n = r^{-n}∫_M f(η_r z)θ(z)dH^n.
2. Continuous compactly supported cutoffs f₁, f₂ with 1_{B̄_κ} ≤ f₁ ≤ 1_{B̄_1} ≤ f₂ ≤ 1_{B̄_{1/κ}}.
3. For r ≤ κr₀ the weighted integrals are integrable, equal lintegrals, and sandwich r^{-n}ν(B̄_r(x)).
4. H^n(P ∩ B̄_s(0)) = ω_n s^n gives ω_nκ^n ≤ ∫_P f₁ and ∫_P f₂ ≤ ω_nκ^{-n}.
5. Pass to the limit r↓0 with Definition 1.7, then let κ↑1: r^{-n}ν(B̄_r(x)) → θ(x)ω_n.
6. Convert to densityRatio: HasDensity n ν x (ofReal θ(x)).

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
