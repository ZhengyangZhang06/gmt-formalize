# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_and_slices-a1.chart_pieces-a1`
- Child DAG node: `root.coarea_and_slices-a1.chart_pieces-a1.lipschitz_open_charts-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 1-4. These rest on Simon Ch. 3, Lemma 1.2 and Remark 1.3 (chapter-03.txt lines 25-73): an embedded submanifold has local C¹ representations ψ : V → ℝ^{n+ℓ}, and such maps 'are automatically Lipschitz in each closed ball ⊂ V'. They also follow the procedure of the area formula (lines 376-381). Specialisations, stated explicitly:
- The submanifold cover that the parent obtains from Lemma 1.2 in its step 1 is a hypothesis here.
- The properness clause of IsC1Submanifold is not used.
- The parent's second Lindelöf step ('countably many of the balls B_{r_u}(u) cover V′') is carried out through a countable basis of ℝⁿ. The pieces D_α are therefore basis sets contained in such balls.
Notation: B(u, r) is the open ball, closedBall(u, r) the closed ball, and Dφ(u) = fderiv ℝ φ u.
Call a pair (D, φ), with D ⊆ ℝⁿ and φ : ℝⁿ → ℝᴺ, good if:
(G1) D is open;
(G2) φ is C¹ on D;
(G3) φ is injective on D;
(G4) φ is Lipschitz on D with some constant in ℝ≥0;
(G5) Dφ(u) is injective for every u ∈ D;
(G6) f∘φ is Lipschitz on D with some constant.
(G1)-(G6) are exactly the first six conjuncts of the conclusion for a pair (D_α, ψ_α).
1. (Charts.) For every i ∈ ℕ and y ∈ S_i, IsC1Submanifold n (S_i) provides an open V_{i,y} ⊆ ℝⁿ, an open W_{i,y} ⊆ ℝᴺ with y ∈ W_{i,y}, and ψ_{i,y} : ℝⁿ → ℝᴺ. The map ψ_{i,y} is C¹ on V_{i,y}, injective on V_{i,y}, satisfies ψ_{i,y}(V_{i,y}) = W_{i,y} ∩ S_i, and Dψ_{i,y}(u) is injective for every u ∈ V_{i,y}. Fix such a choice for all (i, y).
2. (Countably many charts per S_i; Lindelöf in ℝᴺ.) Fix i. ℝᴺ is second countable and the sets W_{i,y}, y ∈ S_i, are open. So there is a countable T_i ⊆ S_i with ⋃_{y∈T_i} W_{i,y} = ⋃_{y∈S_i} W_{i,y} (TopologicalSpace.isOpen_biUnion_countable). Since y ∈ W_{i,y} for every y ∈ S_i, S_i ⊆ ⋃_{y∈T_i} W_{i,y}.
3. (The enumeration.) Let 𝔅 be a countable basis of the topology of ℝⁿ (TopologicalSpace.exists_countable_basis); its members are open sets. Let 𝒬 consist of the pair (∅, 0) together with all pairs (B, ψ_{i,y}) with i ∈ ℕ, y ∈ T_i and B ∈ 𝔅. Let 𝒫 := {p ∈ 𝒬 : p is good}.
- 𝒬 is countable: it is one point plus a countable union over i ∈ ℕ of countable unions over y ∈ T_i of the countable sets {(B, ψ_{i,y}) : B ∈ 𝔅}. Hence 𝒫 is countable.
- The pair (∅, 0) is good. ∅ is open, and (G2)-(G6) hold vacuously on ∅: every map is C¹, injective and K-Lipschitz on ∅ for any K, e.g. K = 0, and there is no u ∈ ∅.
- So 𝒫 is countable and nonempty, and there is a surjection ℕ → 𝒫, α ↦ (D_α, ψ_α) (Set.Countable.exists_eq_range).
Each (D_α, ψ_α) ∈ 𝒫 is good, which proves the first six conjuncts.
4. (Coverage: a point of M off N₀ lies in a chart.) Let x ∈ M; we show x ∈ N₀ ∪ ⋃_α ψ_α(D_α). If x ∈ N₀ this is clear. Otherwise M ⊆ N₀ ∪ ⋃_i S_i gives i with x ∈ S_i, and step 2 gives y ∈ T_i ⊆ S_i with x ∈ W_{i,y}. Write V := V_{i,y} and ψ := ψ_{i,y}. Then x ∈ W_{i,y} ∩ S_i = ψ(V), so x = ψ(u) for some u ∈ V. Moreover x ∈ U because M ⊆ U.
5. (A good radius at u.) Since f is locally Lipschitz on U and x ∈ U, there are K ∈ ℝ≥0 and t ∈ 𝓝[U] x with f K-Lipschitz on t. As U is open, 𝓝[U] x = 𝓝 x, so B(x, s) ⊆ t for some s > 0, and f is K-Lipschitz on B(x, s). ψ is continuous on V (C¹ implies continuous) and V is an open neighbourhood of u, so ψ is continuous at u. Since x = ψ(u), V ∩ ψ⁻¹(B(x, s)) is then a neighbourhood of u. Choose δ > 0 with B(u, δ) ⊆ V ∩ ψ⁻¹(B(x, s)) and put r := δ/2 > 0. Then closedBall(u, r) ⊆ B(u, δ) ⊆ V and ψ(closedBall(u, r)) ⊆ B(x, s).
6. (Lipschitz bound for ψ.) closedBall(u, r) is convex and compact (ℝⁿ is proper) and contained in V, on which ψ is C¹. A C¹ map on a compact convex set is Lipschitz there: its derivative is continuous, hence bounded on the compact set, and the mean value inequality applies (Mathlib ContDiffOn.exists_lipschitzOnWith with smoothness 1 ≠ 0). So ψ is L-Lipschitz on closedBall(u, r) for some L ∈ ℝ≥0.
7. (A good basis set at u.) B(u, r) is open and contains u, so there is B ∈ 𝔅 with u ∈ B ⊆ B(u, r) ⊆ closedBall(u, r) ⊆ V. The pair (B, ψ) is good:
(G1) B is open, being a basis set.
(G2), (G3) ψ is C¹ and injective on V ⊇ B.
(G4) ψ is L-Lipschitz on B ⊆ closedBall(u, r).
(G5) For v ∈ B ⊆ V, Dψ(v) is injective by step 1; fderiv is the derivative at the point and does not depend on the set.
(G6) ψ maps B into ψ(closedBall(u, r)) ⊆ B(x, s), on which f is K-Lipschitz, and ψ is L-Lipschitz on B. So f∘ψ is (K·L)-Lipschitz on B (composition of Lipschitz maps, LipschitzOnWith.comp with MapsTo).
8. (Conclusion.) Since i ∈ ℕ, y ∈ T_i and B ∈ 𝔅, the pair (B, ψ_{i,y}) lies in 𝒬. It is good by step 7, so it belongs to 𝒫. By surjectivity there is α with (D_α, ψ_α) = (B, ψ_{i,y}). Then u ∈ D_α and x = ψ_α(u) ∈ ψ_α(D_α). Hence M ⊆ N₀ ∪ ⋃_α ψ_α(D_α), which is the last conjunct. ∎

## Key steps

1. Choose IsC1Submanifold charts (V_{i,y}, W_{i,y}, ψ_{i,y}) for every i and y ∈ S_i; Lindelöf in ℝᴺ gives a countable T_i ⊆ S_i with S_i ⊆ ⋃_{y∈T_i} W_{i,y}.
2. Fix a countable basis 𝔅 of ℝⁿ. The good pairs among (∅, 0) and (B, ψ_{i,y}) (i ∈ ℕ, y ∈ T_i, B ∈ 𝔅) form a countable nonempty set. Enumerate it surjectively by ℕ; this gives the six chart properties.
3. Coverage: x ∈ M \ N₀ lies in W_{i,y} ∩ S_i = ψ_{i,y}(V_{i,y}) for some y ∈ T_i, so x = ψ_{i,y}(u) with u ∈ V_{i,y}, and x ∈ U.
4. Local Lipschitz continuity of f at x and continuity of ψ_{i,y} at u give r > 0 with closedBall(u, r) ⊆ V_{i,y} and ψ_{i,y}(closedBall(u, r)) inside a ball where f is Lipschitz. ψ_{i,y} is Lipschitz on that compact convex closed ball (C¹ ⇒ Lipschitz).
5. A basis set B with u ∈ B ⊆ B(u, r) makes (B, ψ_{i,y}) good (by restriction and composition), so it equals some (D_α, ψ_α) and x ∈ ψ_α(D_α).

## Reference use

### local-project

Queries:
- `rg -n "^def IsC1Submanifold|^def SubmanifoldCoverCharacterization" project/GMT/Ch03/Contract.lean`
- `rg -n "theorem ContDiffOn.exists_lipschitzOnWith|theorem LipschitzOnWith.extend_finite_dimension|theorem LipschitzOnWith.extend_pi|theorem measurableSet_of_differentiableAt|theorem measurable_fderiv|theorem LipschitzWith.ae_differentiableAt|theorem measurableSet_eq_fun|theorem LipschitzOnWith.hausdorffMeasure_image_le|euclideanHausdorffMeasure_eq_volume|theorem isOpen_iUnion_countable|theorem isOpen_biUnion_countable|theorem Convex.lipschitzOnWith_of_nnnorm_fderiv_le|theorem HasFDerivAt.congr_of_eventuallyEq|theorem ContDiffOn.continuousOn_fderiv_of_isOpen" mathlib/Mathlib`
- `rg -n "theorem IsLindelof.indexed_countable_subcover|theorem HereditarilyLindelofSpace.isLindelof|theorem Set.Countable.exists_eq_range" -A 4 mathlib/Mathlib`
- `rg -l "exists_contDiff.*fderiv.*ne|lipschitz.*contDiff.*approx|C\^1 approximation|Whitney extension" mathlib/Mathlib`
- `rg -n "euclideanHausdorffMeasure_image_le_of_lipschitzOn|exists_lipschitz_extension_finiteDimensional" Poincare (simongmt package)`
- `rg -n "^(theorem|lemma|def|noncomputable def|structure|abbrev)" Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n "theorem .*c1_approx|theorem .*C1Approx|theorem .*contDiff_approximation|theorem .*whitney" Poincare/SimonGMT/Chapter02/*.lean`
- `grep -c / rg -l for submanifold_cover_lipschitz_open_charts and lipschitzOn_open_c1_first_order_agreement in dag.json, DAG.md, issue-workers.json, simongmt Poincare and mathlib/Mathlib (name-collision check)`
- `lake env lean GMT/Scratch/ChartPiecesSplitCheck.lean, ChartPiecesSplitApi.lean, ChartPiecesSplitChildA.lean, ChartPiecesSplitChildB.lean, ChartPiecesSplitFull.lean (replayed Contract scope of gmt-compare.py contract_scope); lean_contract.validate_lean_statement on both child types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Compactness/Lindelof.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`

Snapshot: project d09bc8a (frozen Contract only), Mathlib 25730c7c and the pinned simongmt package. No match for either child. Mathlib has no C¹-approximation or first-order-agreement lemma for Lipschitz maps: the rg query for C¹-approximation/Whitney names found no file. SimonGMT Chapter02 has only Whitney-extension internals. SimonGMT SubmanifoldCover.lean proves only the converse 'if' direction, for its own IsSimonSubmanifold, and has no chart-piece cover for the contract's IsC1Submanifold. Hence both obligations are supplied as children. Every tool cited in the child proofs exists in the stated form: TopologicalSpace.isOpen_biUnion_countable, TopologicalSpace.exists_countable_basis, Set.Countable.exists_eq_range, ContDiffOn.exists_lipschitzOnWith (n ≠ 0, convex, compact), LipschitzOnWith.comp, IsOpen.nhdsWithin_eq, LipschitzOnWith.extend_finite_dimension, measurableSet_of_differentiableAt, measurable_fderiv, measurableSet_eq_fun (its MeasurableEq instance resolves for ℝⁿ →L[ℝ] ℝᵐ), LipschitzWith.ae_differentiableAt, HasFDerivAt.congr_of_eventuallyEq and ENNReal.tendsto_inv_nat_nhds_zero. For the parent assembly they include SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn and EuclideanSpace.euclideanHausdorffMeasure_eq_volume. SimonGMT exists_lipschitz_extension_finiteDimensional is not imported by the Ch03 contract, so the Mathlib extension lemma is cited instead. Lean checks in the replayed Contract scope: both child types validate and elaborate; the assembly from the two child types to the exact frozen parent type compiles; complete proofs of both children compile; everything depends only on propext, Classical.choice and Quot.sound. The proposed names collide with nothing.
