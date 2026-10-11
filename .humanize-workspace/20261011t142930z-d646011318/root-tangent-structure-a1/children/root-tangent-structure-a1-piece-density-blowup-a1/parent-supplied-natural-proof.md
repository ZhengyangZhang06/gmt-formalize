# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_structure-a1`
- Child DAG node: `root.tangent_structure-a1.piece_density_blowup-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent proof, step 3 (blow-up of one Lipschitz piece at a Lebesgue density point; Simon Ch. 3, proof of Theorem 1.6 '⇒' for a parametrized piece, which replaces the embedded C¹ pieces of Lemma 1.2), together with the piece facts of step 1. No errata apply.

Conventions. n ≥ 1, ℓ ≥ 0; E := Ambient n ℓ = EuclideanSpace ℝ (Fin (n+ℓ)); ℝⁿ := EuclideanSpace ℝ (Fin n) with Lebesgue measure Lⁿ := volume; Hⁿ := μHE[n] (on ℝⁿ, Hⁿ = Lⁿ by Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume, and finrank ℝ ℝⁿ = n by finrank_euclideanSpace_fin); B_ρ(z) := closedBall z ρ; ω_n := Lⁿ(ball 0 1).toReal ∈ (0, ∞) and Lⁿ(B_s(z)) = sⁿ·Lⁿ(ball 0 1) for s ≥ 0 (Mathlib Measure.addHaar_closedBall, addHaar_closedBall_eq_addHaar_ball); ‖f‖ := sup|f|; for G: ℝⁿ → E, JG(v) := SimonGMT Chapter02.areaJacobianAt G v = (fderiv ℝ G v).normDet ≥ 0. Hypotheses: (P1) C ⊆ ℝⁿ compact; (P2) F: ℝⁿ → E is κ-Lipschitz (κ ≥ 0); (P3) for every w ∈ C, F is differentiable at w and DF(w) := fderiv ℝ F w is injective; (P4) w ↦ DF(w) is continuous on C; (P5) c > 0 and c|v − w| ≤ |F(v) − F(w)| for all v, w ∈ C. Put N := F(C).
Library results used (pinned; #print axioms shows only propext, Classical.choice, Quot.sound):
(R2a) SimonGMT Chapter02.weighted_area_formula_lipschitz_injOn: G: ℝⁿ → E Lipschitz, B ⊆ ℝⁿ Borel, G injective on B ⇒ ∫⁻_{G(B)} u dHⁿ = ∫⁻_B ofReal(JG(v))·u(G(v)) dLⁿ(v) for every u: E → [0, ∞].
(R2b) SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn: G K-Lipschitz on S ⇒ Hⁿ(G(S)) ≤ Kⁿ·Hⁿ(S).
(R2c) Mathlib LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume: for linear A: ℝⁿ → E and S ⊆ ℝⁿ, Hⁿ(A(S)) = ofReal(normDet A)·Lⁿ(S).
(R2d) SimonGMT Chapter02.continuous_normDet: A ↦ normDet A is continuous on L(ℝⁿ, E); Chapter02.measurable_areaJacobianAt: JG is Borel.

Proof.

1. Preliminary facts.
(a) F is injective on C: if F(v) = F(w) with v, w ∈ C then c|v − w| ≤ 0 by (P5), so v = w.
(b) N is compact (continuous image of the compact C), hence Borel, and Hⁿ(N) ≤ κⁿ·Lⁿ(C) < ∞ by (R2b).
(c) v ↦ JF(v) = normDet(DF(v)) is continuous on C by (P4) and (R2d); if C ≠ ∅ it is bounded on the compact set C by some Γ_J ≥ 0 (if C = ∅, claim (3a) is vacuous and (3b) is vacuous).

2. Claim (3b): with Γ := κⁿ·ω_n·c⁻ⁿ ≥ 0, Hⁿ(N ∩ B_ρ(x)) ≤ ofReal(Γρⁿ) for every x ∈ N and ρ > 0.
Let x = F(w) with w ∈ C, and ρ > 0. If y ∈ N ∩ B_ρ(x), write y = F(v) with v ∈ C; then c|v − w| ≤ |F(v) − F(w)| = |y − x| ≤ ρ, so v ∈ C ∩ B_{ρ/c}(w). Hence N ∩ B_ρ(x) ⊆ F(C ∩ B_{ρ/c}(w)). By (R2b) (F is κ-Lipschitz) and Hⁿ = Lⁿ on ℝⁿ,
Hⁿ(N ∩ B_ρ(x)) ≤ κⁿ·Lⁿ(B_{ρ/c}(w)) = κⁿ·(ρ/c)ⁿ·Lⁿ(ball 0 1) = ofReal(Γρⁿ).

3. Set-up for claim (3a). Fix w ∈ C with Lⁿ(C ∩ B_r(w))/Lⁿ(B_r(w)) → 1 as r ↓ 0, and f ∈ C_c(E). Put x := F(w), A := DF(w) (injective by (P3)) and T := range A = A(ℝⁿ). Choose R > 0 with f(z) = 0 whenever |z| > R (f has compact support). Since n ≥ 1, the unit sphere of ℝⁿ is nonempty and compact and e ↦ |Ae| is continuous and positive on it (A injective), so m_A := min_{|e|=1}|Ae| > 0 and |Au| ≥ m_A|u| for all u ∈ ℝⁿ. Put R' := R/min(c, m_A). f is uniformly continuous (continuous with compact support), so there is ω_f: [0, ∞) → [0, ∞) with |f(z) − f(z')| ≤ ω_f(|z − z'|) and ω_f(s) → 0 as s ↓ 0.

4. Area formula on the piece. For t > 0 let g_t(y) := f(t⁻¹(y − x)); g_t is continuous and |g_t| ≤ ‖f‖, so g_t is integrable for Hⁿ⌞N (Hⁿ(N) < ∞). Apply (R2a) with G := F and B := C (Borel, F injective on C by 1(a)) to u := ofReal(g_t⁺) and to u := ofReal(g_t⁻):
∫⁻_N ofReal(g_t^±) dHⁿ = ∫⁻_C ofReal(JF(v)·g_t^±(F(v))) dv,
and both sides are ≤ ‖f‖·Γ_J·Lⁿ(C) < ∞. Subtracting (the Bochner integral of an integrable real function is the difference of the lintegrals of its positive and negative parts):
∫_N g_t dHⁿ = ∫_C JF(v)·f(t⁻¹(F(v) − F(w))) dv.   (4.1)
(Equivalently: Hⁿ⌞N is the image under F of the finite measure JF·Lⁿ⌞C, by (R2a) applied to indicators; then use MeasureTheory.integral_map.)

5. Rescaling. Substituting v = w + tu (Lⁿ is translation invariant and Lⁿ(tS) = tⁿLⁿ(S) for t > 0; Mathlib MeasureTheory.integral_add_left_eq_self and Measure.integral_comp_smul), (4.1) gives
(tⁿ)⁻¹∫_N g_t dHⁿ = ∫_{ℝⁿ} 1_C(w + tu)·JF(w + tu)·f(Q_t(u)) du,  Q_t(u) := t⁻¹(F(w + tu) − F(w)).
If w + tu ∈ C and |u| > R', then by (P5) |Q_t(u)| ≥ t⁻¹·c·|tu| = c|u| > cR' ≥ R, so f(Q_t(u)) = 0. Hence
(tⁿ)⁻¹∫_N g_t dHⁿ = ∫_{B_{R'}(0)} 1_C(w + tu)·JF(w + tu)·f(Q_t(u)) du.   (5.1)

6. The tangent plane. A is linear, injective and Lipschitz (constant ‖A‖), fderiv ℝ A u = A for all u, so JA(u) = normDet(A) = JF(w) for every u. Apply (R2a) with G := A and B := ℝⁿ (A injective) to the positive and negative parts of f (f∘A is bounded and vanishes outside the bounded set B_{R/m_A}(0), so all integrals are finite), obtaining ∫_T f dHⁿ = JF(w)·∫_{ℝⁿ} f(Au) du (alternatively from (R2c): Hⁿ⌞T is the image under A of normDet(A)·Lⁿ). For |u| > R' ≥ R/m_A we have |Au| ≥ m_A|u| > R and f(Au) = 0, so
∫_T f dHⁿ = ∫_{B_{R'}(0)} JF(w)·f(Au) du.   (6.1)

7. Comparison. By (5.1) and (6.1), D_t := (tⁿ)⁻¹∫_N g_t dHⁿ − ∫_T f dHⁿ = D_t' − D_t'' with
D_t' := ∫_{B_{R'}(0)} 1_C(w + tu)·[JF(w + tu)·f(Q_t(u)) − JF(w)·f(Au)] du,
D_t'' := ∫_{B_{R'}(0)} 1_{ℝⁿ∖C}(w + tu)·JF(w)·f(Au) du.
(a) The affine map u ↦ w + tu maps B_{R'}(0) onto B_{tR'}(w) and multiplies Lⁿ by tⁿ, so
|D_t''| ≤ JF(w)·‖f‖·Lⁿ({u ∈ B_{R'}(0) : w + tu ∉ C}) = JF(w)·‖f‖·t⁻ⁿ·Lⁿ(B_{tR'}(w) ∖ C).
C is Borel and 0 < Lⁿ(B_r(w)) < ∞ for r > 0, so Lⁿ(B_r(w) ∖ C)/Lⁿ(B_r(w)) = 1 − Lⁿ(C ∩ B_r(w))/Lⁿ(B_r(w)) → 0 as r ↓ 0 by the density hypothesis, and t⁻ⁿLⁿ(B_{tR'}(w) ∖ C) = R'ⁿ·ω_n·[Lⁿ(B_{tR'}(w) ∖ C)/Lⁿ(B_{tR'}(w))] → 0 as t ↓ 0. Thus D_t'' → 0.
(b) Let σ(s) := sup{|F(w + h) − F(w) − Ah|/|h| : 0 < |h| ≤ s}; σ(s) → 0 as s ↓ 0 because F is differentiable at w with derivative A (P3). Let τ(s) := sup{|JF(v) − JF(w)| : v ∈ C, |v − w| ≤ s}; τ(s) → 0 as s ↓ 0 by the continuity of JF on C at w (1(c)). For |u| ≤ R' with v := w + tu ∈ C we have |Q_t(u) − Au| = t⁻¹|F(w + tu) − F(w) − A(tu)| ≤ |u|·σ(t|u|) ≤ R'·σ(tR') (the left side is 0 if u = 0) and |JF(v) − JF(w)| ≤ τ(tR'); hence
|JF(v)·f(Q_t(u)) − JF(w)·f(Au)| ≤ JF(v)·|f(Q_t(u)) − f(Au)| + |f(Au)|·|JF(v) − JF(w)| ≤ Γ_J·ω_f(R'σ(tR')) + ‖f‖·τ(tR'),
uniformly in such u. Therefore |D_t'| ≤ Lⁿ(B_{R'}(0))·[Γ_J·ω_f(R'σ(tR')) + ‖f‖·τ(tR')] → 0 as t ↓ 0.
Consequently D_t → 0, i.e. (tⁿ)⁻¹∫_{F(C)} f(t⁻¹(y − F(w))) dHⁿ(y) → ∫_{range DF(w)} f dHⁿ as t ↓ 0. This is claim (3a); together with step 2 the theorem is proved. ∎

Implementation note (not part of the argument): the statement elaborates with the frozen imports; the proof additionally needs, e.g., Poincare.SimonGMT.Chapter02.AreaLipschitz and Poincare.SimonGMT.Chapter02.AreaApproximation (already built in the pinned package) and Mathlib.Analysis.InnerProductSpace.NormDet; all seven child types were checked to elaborate unchanged with these imports added.

## Key steps

1. F is injective on C, N := F(C) is compact with Hⁿ(N) < ∞, and JF = normDet∘DF is continuous and bounded by Γ_J on C
2. (3b): N ∩ B_ρ(F(w)) ⊆ F(C ∩ B_{ρ/c}(w)), so Hⁿ(N ∩ B_ρ) ≤ κⁿω_n c⁻ⁿρⁿ by the Lipschitz image bound
3. Area formula on (F, C) for the positive and negative parts: ∫_N f(t⁻¹(y − F(w))) dHⁿ = ∫_C JF(v) f(t⁻¹(F(v) − F(w))) dv
4. Rescale v = w + tu; the integrand vanishes for |u| > R' by the lower Lipschitz bound
5. Area formula for the injective linear A = DF(w): ∫_T f dHⁿ = ∫_{B_{R'}(0)} JF(w) f(Au) du
6. The difference is D_t' − D_t''; D_t'' → 0 because w is a density point, D_t' → 0 by differentiability at w, continuity of JF on C and uniform continuity of f

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `sha256sum <snapshot>/project/GMT/Ch04/Contract.lean GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean`
- `git -C .lake/packages/simongmt rev-parse HEAD`
- `grep -n 'HasWeightedApproximateTangentSpaceAt\|def CountablyRectifiable\|def blowUpMap' -r .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/`
- `grep -n '^theorem\|^def' Chapter04/{WeightedBlowUp,TangentDensity,FirstVariation,Basic}.lean`
- `grep -rn 'weighted_area_formula_lipschitz_injOn|euclideanHausdorffMeasure_image_le_of_lipschitzOn|ae_dimensionalUpperDensity_eq_zero_outside|measure_toOuterMeasure_isBorelRegular|simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure|exists_isClosed_continuousOn_of_measurable|areaJacobian_comp_eq_parametrization_mul_tangential|def areaJacobianAt|planeMeasure_unit_closedBall|hausdorff_blowUp_image' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -rn 'continuous.*normDet|measurable_areaJacobianAt' .lake/packages/simongmt/Poincare/SimonGMT`
- `rg -n 'theorem .*[Ll]usin|lusin' <snapshot>/mathlib/Mathlib`
- `rg -n 'measure_eq_zero_iff_ae_notMem|ofReal_le_enorm|Regular.smul|exists_isClosed_sdiff_lt' <snapshot>/mathlib/Mathlib`
- `grep -rn 'InnerProductSpace.volume_closedBall|hasDerivAt_integral_of_dominated_loc_of_deriv_le|isSymmSndFDerivAt|inverse_continuousAt|normDet_comp|def normDet|euclideanHausdorffMeasure_eq_volume' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem integral_withDensity_eq_integral_toReal_smul₀' <snapshot>/mathlib/Mathlib`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/ch04-ts-decomp/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/ch04-ts-decomp/olean lean /tmp/ch04-ts-decomp/{T0,T1,T5}.lean (statement-scope availability of LinearMap.range/normDet/adjoint; instance #synth)`
- `python3 /tmp/ch04-ts-decomp/scripts/gen.py (verifier gmt-compare.child_modules + lean_contract.validate_lean_statement); lean /tmp/ch04-ts-decomp/gen/Challenge_*.lean`
- `lean /tmp/ch04-ts-decomp/T6.lean (parent assembly from sorry'd children and sibling)`
- `lake env lean /tmp/ch04-ts-decomp/Axioms.lean (#print axioms of the cited lemmas)`
- `lean /tmp/ch04-ts-decomp/gen2/WithImports.lean /tmp/ch04-ts-decomp/gen2/Synth.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-lipschitz-pieces-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/MetricSpace/CantorScheme.lean`
- `/tmp/ch04-ts-decomp/T6.lean`
- `/tmp/ch04-ts-decomp/Axioms.lean`
- `/tmp/ch04-ts-decomp/gen2/WithImports.lean`

Contract and pinned packages:
- The snapshot contract (sha256 6e58e5dd…0f4770b) is byte-identical to the workspace Contract.lean and Submission.lean.
- SimonGMT is at the pinned revision 2b3663083f3fe399b6296fb8eaee52169170e197.

What can appear in a child type:
- In the frozen statement scope (`import GMT.Ch04.Submission` plus the contract opens), LinearMap.normDet, ContinuousLinearMap.adjoint and LinearMap.adjoint are unknown constants. So no child type mentions Jacobians or adjoints.
- `LinearMap.range (fderiv ℝ F w)` does not elaborate; `LinearMap.range (fderiv ℝ F w).toLinearMap` does, and the child types use that form.

Lusin's theorem:
- The snapshot Mathlib has no Lusin theorem: `rg 'theorem .*[Ll]usin'` only hits a docstring in Topology/MetricSpace/CantorScheme.lean.
- SimonGMT Chapter01.exists_isClosed_continuousOn_of_measurable is cited instead.

Cited library results — each exists with the stated meaning, and #print axioms shows only propext, Classical.choice, Quot.sound:
- SimonGMT Chapter04: map_inverse_blowUp_carrier, hausdorff_blowUp_image, planeMeasure_unit_closedBall, tangentDensityCutoff_eq_one, RectifiableVarifold.integral_weighted_blowUp.
- SimonGMT Chapter02: continuous_normDet, measurable_areaJacobianAt, weighted_area_formula_lipschitz_injOn, euclideanHausdorffMeasure_image_le_of_lipschitzOn, simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure, areaJacobian_comp_eq_parametrization_mul_tangential.
- SimonGMT Chapter01: exists_isClosed_continuousOn_of_measurable, ae_dimensionalUpperDensity_eq_zero_outside, measure_toOuterMeasure_isBorelRegular.
- SimonGMT Chapter03: regular_euclideanHausdorffMeasure_restrict_submodule, support_euclideanHausdorffMeasure_restrict_submodule.
- Mathlib: Besicovitch.ae_tendsto_measure_inter_div, Measure.ext_of_integral_eq_on_compactlySupported, hasDerivAt_integral_of_dominated_loc_of_deriv_le, ContDiffAt.isSymmSndFDerivAt, NormedRing.inverse_continuousAt, InnerProductSpace.volume_closedBall, LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume, LinearMap.normDet_sq_eq_det_gram, LinearMap.normDet_comp, MeasurableSet.exists_isClosed_sdiff_lt, Measure.Regular.smul.
- integral_withDensity_eq_integral_toReal_smul₀ is a root-namespace lemma in MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean.

Elaboration checks:
- All seven child types pass the verifier's validate_lean_statement.
- Each compiles as a comparator-generated NodeChallenge file, with only the expected sorry warning.
- They still elaborate when the implementation imports are added, with the same instances; for example, volume on EuclideanSpace stays measureSpaceOfInnerProductSpace.

Parent assembly:
- T6.lean declares the seven children and the sibling rectifiable_lipschitz_piece_cover as sorry'd theorems, then gives a full proof of Submission.tangent_structure_first_variation with exactly the frozen type.
- It compiles with only the eight sorry warnings.
