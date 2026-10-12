# Parent-supplied natural-language proof

- Parent DAG node: `root.canonical_representatives-a1`
- Child DAG node: `root.canonical_representatives-a1.canonical_closed_support-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions.
- Hⁿ = μHE[n]; B_ρ(x) = closedBall x ρ; ω_n = omega n; μ = V.weight; Θ = V.density; M_V = V.canonicalCarrier U = {x | x ∈ U ∧ 0 < Θ(x)}.
- spt V = V.support = μ.support. A point x lies in μ.support iff every neighbourhood of x has positive μ-measure (Measure.mem_support_iff_forall).
- UpperSemicontinuousOn Θ U means: for x ∈ U and y > Θ(x), eventually for x' in 𝓝[U] x, Θ(x') < y.
- For a pair b = (M', θ'), (mk b).weight = pairWeight n M' θ' = (Hⁿ⌞M').withDensity(x ↦ ENNReal.ofReal θ'(x)) by definition.
- 𝓝[>] 0 is a nontrivial filter on ℝ.

1. Relative closedness (first conjunct). Fix α > 0. By upper semicontinuity of Θ on U there is a closed set C with U ∩ {x | α ≤ Θ(x)} = U ∩ C (Mathlib upperSemicontinuousOn_iff_preimage_Ici). [Directly: let S := {x ∈ U | α ≤ Θ(x)} and C := closure S, so S ⊆ U ∩ C. Let x ∈ U ∩ C and y > Θ(x). Upper semicontinuity gives a neighbourhood W of x with Θ < y on W ∩ U. Since x ∈ closure S, W meets S ⊆ U, so α ≤ Θ(x') < y for some x' ∈ W ∩ S. As y > Θ(x) is arbitrary, α ≤ Θ(x), i.e. x ∈ S.] Because α > 0, α ≤ Θ(x) implies 0 < Θ(x). Hence {x | x ∈ M_V ∧ α ≤ Θ(x)} = {x | x ∈ U ∧ α ≤ Θ(x)} = U ∩ C = C ∩ U, as required.

2. Set-up for the second conjunct. Let α > 0 with V.MultiplicityGE α U: there is an admissible pair b = (M', θ') with mk b = V and α ≤ θ'(x) for Hⁿ⌞(M' ∩ U)-a.e. x. Replace V by mk b; then μ = (Hⁿ⌞M').withDensity(ENNReal.ofReal ∘ θ').

3. Θ ≥ α μ-a.e. in U.
(a) ApproxTangentAE applied to n, ℓ, b (with n > 0) gives (mk b).HasDensityAt x (θ' x) for Hⁿ⌞M'-a.e. x, i.e. μ.real(B_ρ(x)) / (ω_n ρⁿ) → θ'(x) along 𝓝[>] 0. By uniqueness of limits, Θ(x) = θ'(x) (Filter.Tendsto.limUnder_eq).
(b) U is open, hence measurable, so Hⁿ⌞(M' ∩ U) = (Hⁿ⌞M')⌞U (Measure.restrict_restrict). The multiplicity hypothesis becomes: for Hⁿ⌞M'-a.e. x, x ∈ U → α ≤ θ'(x) (ae_restrict_iff').
(c) Combining (a) and (b): for Hⁿ⌞M'-a.e. x, x ∈ U → α ≤ Θ(x).
(d) μ ≪ Hⁿ⌞M' (withDensity_absolutelyContinuous), so for μ-a.e. x, x ∈ U → α ≤ Θ(x). Equivalently, μ({x | ¬(x ∈ U → α ≤ Θ(x))}) = 0 (ae_iff).

4. Θ ≥ α on spt V ∩ U. Let x ∈ spt V ∩ U and suppose Θ(x) < α. Upper semicontinuity at x within U gives: eventually for y in 𝓝[U] x, Θ(y) < α. Since U is open and x ∈ U, 𝓝[U] x = 𝓝 x (IsOpen.nhdsWithin_eq). Hence W := {y | Θ(y) < α} ∩ U is a neighbourhood of x, and μ(W) > 0 because x ∈ spt μ. But each y ∈ W satisfies y ∈ U and ¬(α ≤ Θ(y)), so W ⊆ {y | ¬(y ∈ U → α ≤ Θ(y))}, a μ-null set by step 3. Thus μ(W) = 0, a contradiction. Therefore α ≤ Θ(x) for all x ∈ spt V ∩ U.

5. M_V ⊆ spt V. Let x ∈ M_V, so x ∈ U and Θ(x) > 0. By hypothesis q(ρ) := μ.real(B_ρ(x)) / (ω_n ρⁿ) → Θ(x) > 0 along 𝓝[>] 0, so q(ρ) > 0 for all ρ in some member of 𝓝[>] 0. Let N be a neighbourhood of x and choose r > 0 with B_r(x) ⊆ N. Since (0, r) ∈ 𝓝[>] 0 and the filter is nontrivial, there is ρ ∈ (0, r) with q(ρ) > 0. Then μ.real(B_ρ(x)) ≠ 0, since otherwise q(ρ) = 0. So μ(B_ρ(x)) ≠ 0, because μ.real is (μ ·).toReal and the toReal of 0 is 0. Hence μ(N) ≥ μ(B_ρ(x)) > 0, since B_ρ(x) ⊆ B_r(x) ⊆ N. As N was arbitrary, x ∈ spt μ = spt V.

6. Conclusion of the second conjunct. By step 5 and M_V ⊆ U, M_V ⊆ spt V ∩ U. Conversely, if x ∈ spt V ∩ U then Θ(x) ≥ α > 0 by step 4, so x ∈ M_V. Hence M_V = spt V ∩ U. For x ∈ M_V we have x ∈ spt V ∩ U, so α ≤ Θ(x) by step 4. Together with step 1 this proves the statement. ∎

## Key steps

1. Upper semicontinuity gives a closed C with U ∩ {Θ ≥ α} = U ∩ C; α > 0 gives {x ∈ M_V : Θ ≥ α} = C ∩ U
2. MultiplicityGE, ApproxTangentAE (Θ = θ' a.e. on M') and μ_V ≪ Hⁿ⌞M' give Θ ≥ α μ_V-a.e. in U
3. At a support point in U with Θ < α, upper semicontinuity gives a neighbourhood of positive measure where Θ < α, a contradiction
4. Θ(x) > 0 forces μ_V(B_ρ(x)) > 0 for small ρ, so x ∈ spt V
5. Hence M_V = spt V ∩ U and Θ ≥ α on M_V

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
