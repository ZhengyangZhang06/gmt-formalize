# Parent-supplied natural-language proof

- Parent DAG node: `root.canonical_representatives-a1`
- Child DAG node: `root.canonical_representatives-a1.hausdorff_null_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. E = Ambient n ℓ = EuclideanSpace ℝ (Fin (n + ℓ)) is a finite-dimensional real inner-product space. It is proper (closed balls are compact), locally compact, σ-compact and metrizable, and carries its Borel σ-algebra. Hⁿ = μHE[n]; B_ρ(x) = closedBall x ρ; ω_n = omega n = (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal; μ.real S = (μ S).toReal. For an arbitrary S ⊆ E, μ(S) is the outer measure.
From the pinned SimonGMT package (namespace Poincare.SimonGMT, revision 2b3663083f3f):
- ω'_n := Chapter01.realUnitBallVolume (n : ℝ) = ENNReal.ofReal (π^{n/2} / Γ(n/2 + 1)).
- For an outer measure ν on E, S ⊆ E, x ∈ E and r ∈ ℝ, Q_ν(S, x, r) := ν(S ∩ B_r(x)) / (ω'_n · ENNReal.ofReal(r)^{(n : ℝ)}) ∈ [0, ∞]. This is Chapter01.dimensionalDensityQuotient ν (n : ℝ) S x r.
- Θ*(ν, S, x) := limsup of Q_ν(S, x, r) as r → 0+, the limsup along 𝓝[>] 0. This is Chapter01.dimensionalUpperDensity ν (n : ℝ) S x.
- H_S := Chapter01.simonHausdorffOuterMeasureReal (n : ℝ), Simon's n-dimensional Hausdorff outer measure.
Simon Ch. 1, Theorem 3.3 is Chapter01.simon_theorem_3_3: if ν is a Borel-regular outer measure on a metric space, 0 ≤ n, A₁ ⊆ A₂, 0 ≤ t, and ENNReal.ofReal t ≤ Θ*(ν, A₂, x) for every x ∈ A₁, then ENNReal.ofReal t · H_S(A₁) ≤ ν(A₂).
The modules Poincare.SimonGMT.Chapter01.DensityComparison, Poincare.SimonGMT.Chapter01.EuclideanHausdorffUpper and Poincare.SimonGMT.Chapter02.AreaLiteral are not in the import closure of GMT.Ch04.Submission, so the implementation must import them. Every SimonGMT lemma cited below depends only on propext, Classical.choice and Quot.sound.

1. Normalisation of ω_n. Chapter01.volume_euclidean_ball_eq (which requires n > 0) at centre 0 and radius 1 gives volume(ball 0 1) = ω'_n · ENNReal.ofReal(1)^n = ω'_n. Hence ω_n = (ω'_n).toReal. Since ω'_n ≠ ∞ (Chapter01.realUnitBallVolume_ne_top), ENNReal.ofReal ω_n = ω'_n. Since ω'_n > 0 (Chapter01.realUnitBallVolume_pos, as 0 ≤ (n : ℝ)), also ω_n > 0.

2. Normalisation of Hⁿ. For every S ⊆ E, H_S(S) = Hⁿ(S). By Chapter01.simonHausdorffMeasureReal_toOuterMeasure (with 0 ≤ (n : ℝ)), H_S is the outer measure of the measure Chapter01.simonHausdorffMeasureReal (n : ℝ). Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure identifies that measure with μHE[n] on the metric space E with its Borel σ-algebra.

3. A small open set around A. μ is finite on compact sets and E is locally compact, so μ is locally finite. As E is σ-compact and metrizable, μ is regular (Mathlib instance Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure), in particular outer regular. Fix ε ∈ [0, ∞] with ε > 0. Because μ(A) = 0 < ε, Set.exists_isOpen_lt_of_lt yields an open set O ⊇ A with μ(O) < ε.

4. The upper density of μ relative to O is at least t on A. Fix x ∈ A and, by hypothesis, a real s ≥ t with q(ρ) := μ.real(B_ρ(x)) / (ω_n ρⁿ) → s as ρ → 0+. As O is open and x ∈ O, there is r > 0 with B_r(x) ⊆ O. Let 0 < ρ < r. Then:
- O ∩ B_ρ(x) = B_ρ(x);
- μ(B_ρ(x)) < ∞, because B_ρ(x) is compact;
- ENNReal.ofReal(ρ)^{(n : ℝ)} = ENNReal.ofReal(ρ)^n = ENNReal.ofReal(ρⁿ), since ρ ≥ 0;
- by step 1, ω'_n · ENNReal.ofReal(ρⁿ) = ENNReal.ofReal(ω_n) · ENNReal.ofReal(ρⁿ) = ENNReal.ofReal(ω_n ρⁿ), and ω_n ρⁿ > 0.
Therefore Q_μ(O, x, ρ) = μ(B_ρ(x)) / ENNReal.ofReal(ω_n ρⁿ) = ENNReal.ofReal(μ.real(B_ρ(x))) / ENNReal.ofReal(ω_n ρⁿ) = ENNReal.ofReal(q(ρ)). This uses ENNReal.ofReal(μ.real B) = μ(B) for μ(B) < ∞ (ofReal_measureReal) and ENNReal.ofReal(a / b) = ENNReal.ofReal a / ENNReal.ofReal b for b > 0 (ENNReal.ofReal_div_of_pos).
By continuity of ENNReal.ofReal, ENNReal.ofReal(q(ρ)) → ENNReal.ofReal(s) as ρ → 0+. The functions Q_μ(O, x, ·) and ENNReal.ofReal ∘ q agree on (0, r), which belongs to 𝓝[>] 0, so also Q_μ(O, x, ρ) → ENNReal.ofReal(s). The filter 𝓝[>] 0 on ℝ is nontrivial, so the limsup equals the limit: Θ*(μ, O, x) = ENNReal.ofReal(s) ≥ ENNReal.ofReal(t), by monotonicity of ENNReal.ofReal and s ≥ t.

5. Simon's Theorem 3.3. The outer measure induced by the Borel measure μ is Borel regular (Chapter01.measure_toOuterMeasure_isBorelRegular μ). Apply Chapter01.simon_theorem_3_3 to this outer measure with dimension (n : ℝ) ≥ 0, A₁ = A ⊆ A₂ = O (step 3), threshold t ≥ 0 and the bound of step 4. This gives ENNReal.ofReal(t) · H_S(A) ≤ μ(O). By steps 2 and 3, ENNReal.ofReal(t) · Hⁿ(A) ≤ μ(O) < ε.

6. Conclusion. ENNReal.ofReal(t) · Hⁿ(A) ≤ ε for every ε > 0, so ENNReal.ofReal(t) · Hⁿ(A) = 0 (for example by le_of_forall_gt_imp_ge_of_dense). As t > 0, ENNReal.ofReal(t) ≠ 0, hence Hⁿ(A) = 0. ∎

## Key steps

1. ENNReal.ofReal (omega n) = realUnitBallVolume n > 0 (volume_euclidean_ball_eq), and simonHausdorffOuterMeasureReal n = μHE[n] (simonHausdorffMeasureReal_toOuterMeasure plus the AreaLiteral bridge)
2. μ is finite on compacts, hence regular, so there is an open O ⊇ A with μ(O) < ε
3. For x ∈ A, B_r(x) ⊆ O, so Simon's upper density of μ relative to O at x equals ofReal(s) ≥ ofReal(t)
4. Simon Ch. 1 Thm 3.3 (simon_theorem_3_3) gives ofReal(t)·Hⁿ(A) ≤ μ(O) < ε
5. ε is arbitrary and t > 0, so Hⁿ(A) = 0

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `sha256sum <snapshot>/project/GMT/Ch04/Contract.lean GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean`
- `git -C .lake/packages/simongmt rev-parse HEAD; git -C /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt rev-parse HEAD; grep -A3 '"simongmt"' lake-manifest.json`
- `rg -n 'canonicalCarrier|def CanonicalRepresentative|def LpSupportRepresentation|def StationaryDensity|def LpDensity|def MultiplicityGE|def HasDensityAt|def density' <snapshot>/project/GMT/Ch04/Contract.lean`
- `rg -n 'theorem upperSemicontinuousOn_iff_preimage_Ici|theorem upperSemicontinuousOn_iff_preimage_Iio' <snapshot>/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean`
- `rg -n 'theorem _root_.Set.exists_isOpen_lt_of_lt|Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `rg -n 'lemma mem_support_iff_forall' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `rg -n "theorem restrict_apply₀'|theorem restrict_congr_set|theorem restrict_restrict |theorem restrict_mono " <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n 'theorem withDensity_congr_ae|theorem restrict_withDensity |theorem withDensity_absolutelyContinuous ' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `rg -n 'limUnder_eq' <snapshot>/mathlib/Mathlib/Topology/Separation/`
- `rg -n 'theorem ofReal_measureReal' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Real.lean`
- `grep -n 'theorem UpperSemicontinuous.measurable|upperSemicontinuousOn_iff' .lake/packages/mathlib/Mathlib/Topology/Semicontinuity/ .lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/`
- `grep -n 'simon_theorem_3_3|^theorem' simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `grep -rn 'realUnitBallVolume_pos|realUnitBallVolume_ne_top|volume_euclidean_ball_eq|realUnitBallVolume_nat_eq' simongmt/Poincare/SimonGMT/Chapter01/`
- `grep -rn 'def dimensionalUpperDensity|def dimensionalDensityQuotient|def simonHausdorffOuterMeasureReal|def IsBorelRegularOuterMeasure|theorem measure_toOuterMeasure_isBorelRegular|simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure' simongmt/Poincare/`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rln canonicalDensityCarrier simongmt/Poincare/SimonGMT/Chapter04/ (no-match check for a representation theorem on the contract's RectifiableVarifold)`
- `grep -n '3.12|3.13|canonical|4.10' book/chapter-04.txt`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/canrep-audit/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/canrep-audit/olean lean /tmp/canrep-audit/src/Imports.lean (availability of cited lemmas after import GMT.Ch04.Submission)`
- `lake env lean /tmp/canrep-audit/src/Axioms.lean (#print axioms of cited SimonGMT lemmas)`
- `LEAN_PATH=... lean /tmp/canrep-audit/src/ChildTypes.lean and /tmp/canrep-audit/src/NoOpen.lean (child type elaboration and parent assembly)`
- `LEAN_PATH=... lean /tmp/canrep-audit/src/Proofs3.lean (complete proofs of the three children, parent assembly, #print axioms)`
- `grep -o '"lean_name": *"[^"]*"' dag.json nodes/*/decomposition*.json nodes/*/*handoff*.json (name-collision check)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.lake/packages/simongmt/Poincare/SimonGMT.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/EuclideanHausdorffUpper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/CanonicalDensitySupport.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Density.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-canonical-representatives-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-canonical-representatives-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-canonical-representatives-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root/speculative-prompt-v2.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/tmp/canrep-audit/src/Imports.lean`
- `/tmp/canrep-audit/src/Axioms.lean`
- `/tmp/canrep-audit/src/ChildTypes.lean`
- `/tmp/canrep-audit/src/Proofs.lean`
- `/tmp/canrep-audit/src/Proofs3.lean`
- `/tmp/canrep-audit/src/NoOpen.lean`

The snapshot manifest pins project ff75f52a… and Mathlib 25730c7c…; the snapshot Contract.lean and the workspace Contract.lean/Submission.lean share sha256 6e58e5dd…0f4770b, and SimonGMT is at the pinned 2b3663083f3f… in both .lake/packages/simongmt and lake-packages-25730c7c/simongmt. Contract lines 145–185 define density, HasDensityAt, MultiplicityGE and canonicalCarrier; lines 266–283 and 353–369 give StationaryDensity, CanonicalRepresentative, LpDensity and LpSupportRepresentation. No-match result: SimonGMT has no representation theorem V = v(M_V, θ_V) for the contract's RectifiableVarifold. canonicalDensityCarrier and isClosed_canonicalDensity_superlevel (Chapter04/Density.lean) and IsStationaryIn.simon_3_13_support (Chapter04/CanonicalDensitySupport.lean) are stated only for the strengthened Chapter04.RectifiableVarifold, and README marks the representation as missing; they serve only as a proof template for the support step. Reusable inputs, all with axioms ⊆ {propext, Classical.choice, Quot.sound}, are SimonGMT Chapter01.simon_theorem_3_3, measure_toOuterMeasure_isBorelRegular, simonHausdorffMeasureReal_toOuterMeasure, volume_euclidean_ball_eq, realUnitBallVolume_pos/_ne_top and Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure. simon_theorem_3_3, volume_euclidean_ball_eq and the AreaLiteral bridge are NOT in the import closure of GMT.Ch04.Submission, so the density child's implementation must import Chapter01.DensityComparison, Chapter01.EuclideanHausdorffUpper and Chapter02.AreaLiteral. Mathlib inputs: upperSemicontinuousOn_iff_preimage_Ici (Semicontinuity/Basic.lean:918); Set.exists_isOpen_lt_of_lt (Regular.lean:359) with the instance Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (:1183); Measure.mem_support_iff_forall (Support.lean:75); restrict_mono, restrict_congr_set, restrict_apply₀' and restrict_restrict (Restrict.lean:89/104/136/205); withDensity_congr_ae, withDensity_absolutelyContinuous and restrict_withDensity (WithDensity.lean:88/146/215); Filter.Tendsto.limUnder_eq (Separation/Hausdorff.lean:296); ofReal_measureReal (Measure/Real.lean:65). Chapter03.CountablyRectifiable is used through its definition. With Submission compiled to an olean, the three child types elaborate in namespace GMT.Ch04 after import GMT.Ch04.Submission. Complete sorry-free proofs of all three children compile with standard axioms only, and the parent assembly from the children plus sorry'd stand-ins for the frozen sibling types elaborates to exactly the frozen type of canonical_representatives. None of the proposed names collides with a reserved name.
