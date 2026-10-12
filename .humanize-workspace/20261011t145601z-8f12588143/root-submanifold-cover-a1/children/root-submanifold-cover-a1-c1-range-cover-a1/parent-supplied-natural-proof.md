# Parent-supplied natural-language proof

- Parent DAG node: `root.submanifold_cover-a1`
- Child DAG node: `root.submanifold_cover-a1.c1_range_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon, Ch. 3, proof of Lemma 1.2, chapter-03.txt lines 61-65 (printed p. 70), applied to a single C¹ map G : ℝⁿ → ℝᵖ:
"Now by the area formula Lⁿ({x : J_{G_ij} = 0} [parent erratum (iii): Hⁿ(G_ij({x : J_{G_ij}(x) = 0})) = 0] whereas if the Jacobian G_ij is non-zero at a point x, then there is a σ > 0 such that G_ij(B_σ(x)) is an n-dimensional C¹ submanifold ... So ∪_{ij} G_ij can be written as the union of a set of measure zero and countably many n-dimensional C¹ submanifolds of ℝ^{n+ℓ}".
This is Steps 6 and 8 of the parent proof (node root.submanifold_cover-a1). Step 7 is the sibling regular_ball_submanifold (Lean: c1_regular_point_ball_image_isC1Submanifold).

Notation: ℝᵈ = EuclideanSpace ℝ (Fin d); B_r(x) = Metric.ball x r; DG(z) = fderiv ℝ G z; Hⁿ = μHE[n]; Lⁿ = volume, which equals μHE[n] on ℝⁿ (EuclideanSpace.euclideanHausdorffMeasure_eq_volume).

Hypotheses: n, p ∈ ℕ; G : ℝⁿ → ℝᵖ with ContDiff ℝ 1 G.
Goal: N₀ ⊆ ℝᵖ and (N_k)_{k∈ℕ} with Hⁿ(N₀) = 0, IsC1Submanifold n (N_k) for every k, and range G ⊆ N₀ ∪ ⋃_k N_k.

1. Critical and regular sets. G is C¹, so it is differentiable at every point with derivative DG(z) (ContDiff.differentiable).
Let Crit(G) := {z ∈ ℝⁿ : DG(z) is not injective} and Reg(G) := ℝⁿ ∖ Crit(G).
With JG(z) := normDet(DG(z)) = √det(DG(z)* DG(z)), we have Crit(G) = {JG = 0} (Mathlib LinearMap.normDet_eq_zero_tfae; SimonGMT Chapter02.areaJacobianAt_eq_zero_iff_not_injective).
Since G is differentiable everywhere, Crit(G) = {z : G is differentiable at z and DG(z) is not injective}.

2. The critical image is Hⁿ-null (parent Step 6). Put N₀ := G(Crit(G)).
For k ∈ ℕ let s_k := B_k(0), an open, convex, bounded set.
- DG is continuous, hence bounded by some C_k on the compact B̄_k(0). By the mean value inequality, G is C_k-Lipschitz on the convex set s_k.
- Crit(G) = {JG = 0} is closed, since JG is the continuous normDet composed with the continuous z ↦ DG(z). So the weight w := 1_{Crit(G)} is Borel.
Apply the weighted area formula for Lipschitz maps on Lebesgue-measurable domains (Simon Ch. 2 (3.5); SimonGMT Chapter02.weighted_area_formula_lipschitzOn_fiberSum with s := s_k, f := G, and this w):
∫ Σ_{z ∈ s_k ∩ G⁻¹(y)} 1_{Crit(G)}(z) dHⁿ(y) = ∫_{s_k} J_G^{s_k}(z) 1_{Crit(G)}(z) dLⁿ(z).
Here J_G^{s_k}(z) = normDet(fderivWithin ℝ G s_k z) = JG(z) for z in the open set s_k.
- The right side is 0, because JG = 0 on Crit(G).
- The left integrand is Hⁿ-a.e. measurable (SimonGMT aemeasurable_weightedAreaFiberSum_lipschitzOn), so it vanishes for Hⁿ-a.e. y.
- For y ∈ G(Crit(G) ∩ s_k) the fiber sum is ≥ 1: it contains a term z ∈ Crit(G) ∩ s_k with G(z) = y, of weight 1.
Hence Hⁿ(G(Crit(G) ∩ s_k)) = 0 for every k. Since ℝⁿ = ⋃_k s_k, countable subadditivity gives
Hⁿ(N₀) = Hⁿ(⋃_k G(Crit(G) ∩ s_k)) = 0.
Library form of this step: SimonGMT Chapter02.area_image_criticalSet_eq_zero G states
μHE[finrank ℝ ℝⁿ](G({z : DifferentiableAt ℝ G z ∧ ¬ Injective (DG(z))})) = 0.
By Step 1 that set is Crit(G), and finrank ℝ ℝⁿ = n by finrank_euclideanSpace_fin.

3. Regular balls (parent Step 7). For each x ∈ Reg(G), apply the sibling regular_ball_submanifold to G (which is C¹) and x (where DG(x) is injective). It gives σ_x > 0 such that G(B_{σ_x}(x)) satisfies IsC1Submanifold n.
For x ∈ Crit(G) set σ_x := 1; these balls are never used.

4. Lindelöf (parent Step 8). ℝⁿ is second countable, and {B_{σ_x}(x) : x ∈ Reg(G)} is a family of open sets indexed by Reg(G).
By Mathlib TopologicalSpace.isOpen_biUnion_countable there is a countable T ⊆ Reg(G) with
⋃_{x∈T} B_{σ_x}(x) = ⋃_{x∈Reg(G)} B_{σ_x}(x).
Every x ∈ Reg(G) lies in its own ball (σ_x > 0), so Reg(G) ⊆ ⋃_{x∈T} B_{σ_x}(x). Openness of Reg(G), noted in the parent, is not needed here.

5. Enumeration, padded with ∅ (parent Step 9).
The family 𝒟 := {∅} ∪ {G(B_{σ_x}(x)) : x ∈ T} of subsets of ℝᵖ is countable (the image of the countable T plus one set) and nonempty. So there is a sequence (N_k)_{k∈ℕ} with {N_k : k ∈ ℕ} = 𝒟 (Mathlib Set.Countable.exists_eq_range).
Each N_k is one of:
- ∅, which satisfies IsC1Submanifold n vacuously (the condition quantifies over y ∈ ∅);
- G(B_{σ_x}(x)) for some x ∈ T ⊆ Reg(G), which satisfies IsC1Submanifold n by Step 3.

6. Covering. Let y ∈ range G, say y = G(z).
- If z ∈ Crit(G), then y ∈ G(Crit(G)) = N₀.
- Otherwise z ∈ Reg(G), so by Step 4 z ∈ B_{σ_x}(x) for some x ∈ T. Then y ∈ G(B_{σ_x}(x)) ∈ 𝒟, i.e. y ∈ N_k for some k.
Hence range G ⊆ N₀ ∪ ⋃_k N_k.

7. Conclusion. N₀ and (N_k) satisfy Hⁿ(N₀) = 0 (Step 2), IsC1Submanifold n (N_k) for all k (Step 5), and range G ⊆ N₀ ∪ ⋃_k N_k (Step 6). ∎

## Key steps

1. G is differentiable everywhere. Crit(G) = {DG not injective} = {JG = 0}, and Reg(G) is its complement.
2. Hⁿ(G(Crit(G))) = 0 by the weighted area formula on the balls B_k(0) with weight 1_{Crit(G)} (library form: SimonGMT area_image_criticalSet_eq_zero, with finrank ℝ ℝⁿ = n). Set N₀ := G(Crit(G)).
3. For each x ∈ Reg(G), the sibling regular_ball_submanifold gives σ_x > 0 with G(B_{σ_x}(x)) an IsC1Submanifold n.
4. Lindelöf (isOpen_biUnion_countable) gives a countable T ⊆ Reg(G) with Reg(G) ⊆ ⋃_{x∈T} B_{σ_x}(x).
5. Enumerate {∅} ∪ {G(B_{σ_x}(x)) : x ∈ T} by ℕ (∅ is vacuously a submanifold). Then range G ⊆ N₀ ∪ ⋃_k N_k.

## Reference use

### local-project

Queries:
- `rg -n "def IsC1Submanifold|def SubmanifoldCoverCharacterization" project/GMT/Ch03/Contract.lean`
- `rg -n "theorem isOpen_biUnion_countable" mathlib/Mathlib/Topology/Bases.lean`
- `rg -n "theorem LinearMap.injective_iff_antilipschitz" mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `rg -n "theorem norm_image_sub_le_of_norm_hasFDerivWithin_le" mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `rg -n "theorem finrank_euclideanSpace_fin" mathlib/Mathlib`
- `rg -n "theorem Countable.exists_eq_range" mathlib/Mathlib/Data/Set/Countable.lean`
- `rg -n "theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n "theorem ContDiff.continuous_fderiv" mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `rg -n "theorem area_image_criticalSet_eq_zero|theorem area_image_eq_zero_of_critical|theorem areaJacobianAt_eq_zero_iff_not_injective" simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `rg -n "theorem countablyRectifiable_of_submanifold_cover|theorem countablyRectifiable_of_isSimonSubmanifold" simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `rg -n "def IsSimonSubmanifold|def IsSimonLocalRepresentation|def IsProperOnInto" simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `rg -n "theorem weighted_area_formula_lipschitzOn_fiberSum|theorem aemeasurable_weightedAreaFiberSum_lipschitzOn|def areaJacobianWithin" simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `rg -n "theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn" simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `rg -n "exists_open_image_eq_inter|isProperMap_chartMap" simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `rg -n -i "immersion|inverse_function|ImplicitFunction" simongmt/Poincare/SimonGMT`
- `grep -rn "c1_regular_point_ball_image_isC1Submanifold|c1_range_null_union_submanifolds" (SimonGMT, Mathlib, all chapter workspaces and .humanize runs)`
- `lake env lean on scratch copies of the frozen contract: elaborate both child types, compile parent from children + uncle statement, compile both child proofs, #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-submanifold-cover-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-c1-approximation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`

Snapshot: project d09bc8a, Mathlib 25730c7c, plus the pinned simongmt package.

Available and used:
- Contract: IsC1Submanifold (Contract.lean:68) and SubmanifoldCoverCharacterization (:182).
- SimonGMT Chapter02/AreaCritical.lean: area_image_criticalSet_eq_zero (:185) gives μHE[finrank E](f '' {DifferentiableAt ∧ ¬Injective fderiv}) = 0, i.e. parent Step 6 directly; also areaJacobianAt_eq_zero_iff_not_injective (:178).
- SimonGMT Chapter02/AreaDomain.lean: weighted_area_formula_lipschitzOn_fiberSum (:106) and aemeasurable_weightedAreaFiberSum_lipschitzOn (:124), the parent's area-formula route for Step 6.
- SimonGMT Chapter03/SubmanifoldCover.lean: countablyRectifiable_of_submanifold_cover (:152). IsSimonSubmanifold / IsSimonLocalRepresentation (Chapter02/Submanifold.lean:36,47) unpack to IsC1Submanifold; the 6-line ⇐ glue was checked in Lean.
- SimonGMT Chapter02/Lipschitz.lean: euclideanHausdorffMeasure_image_le_of_lipschitzOn (:216).
- Mathlib: EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Measure.lean:187), TopologicalSpace.isOpen_biUnion_countable (Bases.lean:942), Set.Countable.exists_eq_range (Countable.lean:149), LinearMap.injective_iff_antilipschitz (FiniteDimension.lean:242), Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (MeanValue.lean:422), finrank_euclideanSpace_fin (PiL2.lean:205), ContDiff.continuous_fderiv (ContDiff/Defs.lean:1271).

No match, so the obligation is new:
- No SimonGMT or Mathlib lemma says the image of a ball around a regular point of a C¹ map is an embedded (relatively proper) C¹ submanifold. The immersion search finds only Chapter08 C² left-inverse lemmas. SubmanifoldTopology's exists_open_image_eq_inter assumes a chart is already given.
- No existing C¹-range-cover lemma.
- The proposed names lean names collide with nothing.

The verifier elaborates child types after `import GMT.Ch03.Submission` in the Contract scope, and accepts Submission imports from the pinned packages.

Scratch Lean checks: both children are fully proved; the parent compiles from child (B), the frozen lipschitz_c1_approximation statement and the ⇐ glue; axioms are propext, Classical.choice and Quot.sound only.
