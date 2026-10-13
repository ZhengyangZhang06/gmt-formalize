# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_characterizations-a1`
- Child DAG node: `root.tangent_characterizations-a1.chartwise_ae_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 1-2 of the parent proof. Step 1 covers each submanifold by countably many chart images (Lindelöf). Step 2 shows the exceptional set (M ∩ N₀) ∪ ⋃ψ_{j,i}(Z_{j,i}) is Hⁿ-null by (F2). These correspond to Simon Ch. 3, Remark 1.3 and the localisation to the C¹ submanifolds N_j in the proof of Theorem 1.6 '⇒' (chapter-03.txt lines 113-143). The parent's predicate 'there is P with HasWeightedApproximateTangentSpaceAt n M θ x P' is abstracted to an arbitrary Q. This child uses the sibling child hausdorffMeasure_image_null_of_locallyLipschitzOn, called (C) below: if V ⊆ ℝⁿ is open, ψ is locally Lipschitz on V, Z ⊆ V and Lⁿ(Z) = 0, then Hⁿ(ψ(Z)) = 0.

Setting. Fix n, N, M, N₀, (S_j) and Q, and assume:
- Hⁿ(N₀) = 0;
- IsC1Submanifold n S_j for every j;
- M ⊆ N₀ ∪ ⋃_j S_j;
- (H): for every open V ⊆ ℝⁿ and every ψ that is C¹ on V with Dψ(u) injective for u ∈ V, for Lⁿ-a.e. u, (u ∈ V and ψ(u) ∈ M) implies Q(ψ(u)).

1. Charts. Fix j and y ∈ S_j. IsC1Submanifold n S_j provides:
   - an open V_{j,y} ⊆ ℝⁿ;
   - an open W_{j,y} ⊆ ℝ^N with y ∈ W_{j,y};
   - a map ψ_{j,y} : ℝⁿ → ℝ^N that is C¹ on V_{j,y}, with ψ_{j,y}(V_{j,y}) = W_{j,y} ∩ S_j and Dψ_{j,y}(u) injective for every u ∈ V_{j,y}.
   Choose such data for every pair (j, y) with y ∈ S_j. The injectivity-on-V and properness clauses of the definition are not needed.

2. Countable subcover. Fix j. The sets W_{j,y} (y ∈ S_j) are open and ℝ^N is second countable. Hence there is a countable T_j ⊆ S_j with ⋃_{y∈T_j} W_{j,y} = ⋃_{y∈S_j} W_{j,y} (Mathlib TopologicalSpace.isOpen_biUnion_countable). Consequently, if x ∈ S_j, then x ∈ W_{j,x} ⊆ ⋃_{y∈S_j} W_{j,y}. So x ∈ W_{j,y} for some y ∈ T_j, and therefore x ∈ W_{j,y} ∩ S_j = ψ_{j,y}(V_{j,y}).

3. Bad parameters. For j and y ∈ S_j put Z_{j,y} := {u : u ∈ V_{j,y}, ψ_{j,y}(u) ∈ M, and Q(ψ_{j,y}(u)) fails}. Apply (H) to (V_{j,y}, ψ_{j,y}); its hypotheses hold by Step 1. It says the set of u at which '(u ∈ V_{j,y} and ψ_{j,y}(u) ∈ M) implies Q(ψ_{j,y}(u))' fails is Lⁿ-null (ae_iff). Z_{j,y} is contained in that set, so Lⁿ(Z_{j,y}) = 0.

4. Null images. ψ_{j,y} is locally Lipschitz on V_{j,y}. Indeed, let u ∈ V_{j,y}. Since V_{j,y} is open, ψ_{j,y} is C¹ at u (ContDiffOn.contDiffAt), hence Lipschitz on some t ∈ 𝓝 u (Mathlib ContDiffAt.exists_lipschitzOnWith), and t ∈ 𝓝[V_{j,y}] u. Since Z_{j,y} ⊆ V_{j,y} and Lⁿ(Z_{j,y}) = 0, (C) gives Hⁿ(ψ_{j,y}(Z_{j,y})) = 0.

5. Exceptional set. Let E := N₀ ∪ ⋃_{j∈ℕ} ⋃_{y∈T_j} ψ_{j,y}(Z_{j,y}). Each T_j is countable and contained in S_j, so Step 4 applies to every term. By countable subadditivity (measure_iUnion_null_iff, measure_biUnion_null_iff, measure_union_null) and Hⁿ(N₀) = 0, we get Hⁿ(E) = 0.

6. Inclusion. Let x ∈ M such that Q(x) fails.
   - If x ∈ N₀, then x ∈ E.
   - Otherwise, since M ⊆ N₀ ∪ ⋃_j S_j, x ∈ S_j for some j. By Step 2 there are y ∈ T_j and u ∈ V_{j,y} with ψ_{j,y}(u) = x. Then u ∈ V_{j,y}, ψ_{j,y}(u) = x ∈ M and Q(ψ_{j,y}(u)) fails. So u ∈ Z_{j,y}, and x ∈ ψ_{j,y}(Z_{j,y}) ⊆ E because y ∈ T_j.

7. Hence {x : not (x ∈ M implies Q(x))} = {x ∈ M : Q(x) fails} ⊆ E, which is Hⁿ-null. By the definition of almost everywhere (ae_iff, measure_mono_null), ∀ᵐ x ∂Hⁿ, x ∈ M → Q(x). ∎

## Key steps

1. IsC1Submanifold gives for each y ∈ S_j a C¹ chart ψ_{j,y} on open V_{j,y} with injective derivative and ψ_{j,y}(V_{j,y}) = W_{j,y} ∩ S_j, y ∈ W_{j,y} open.
2. Lindelöf: countable T_j ⊆ S_j whose chart images cover S_j.
3. The chart hypothesis makes each bad parameter set Z_{j,y} = {u ∈ V_{j,y} : ψ_{j,y}(u) ∈ M, ¬Q} Lⁿ-null.
4. C¹ on an open set implies locally Lipschitz, so the sibling null-image lemma gives Hⁿ(ψ_{j,y}(Z_{j,y})) = 0.
5. E = N₀ ∪ ⋃_j ⋃_{y∈T_j} ψ_{j,y}(Z_{j,y}) is Hⁿ-null and contains {x ∈ M : ¬Q(x)}.

## Reference use

### local-project

Queries:
- `grep -n "def blowUpMap|def CountablyRectifiable|def HasApproximateTangentSpaceAt|def HasWeightedApproximateTangentSpaceAt|def PurelyUnrectifiable" -A 14 simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rn "blowUpMap" simongmt/Poincare/SimonGMT --include=*.lean`
- `grep -rn "theorem.*euclideanHausdorffMeasure.*smul|theorem euclideanHausdorffMeasure_image|theorem.*image_le_of_lipschitzOn|theorem.*image_null|theorem.*image_eq_zero" simongmt/Poincare/SimonGMT`
- `grep -rn "theorem|lemma" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -rn "ContDiffAt.exists_lipschitzOnWith|ContDiffOn.locallyLipschitzOn|isOpen_iUnion_countable|isOpen_biUnion_countable|integral_withDensity_eq_integral_toReal_smul|withDensity_apply_eq_zero" mathlib/Mathlib`
- `grep -rn "Integrable.lintegral_lt_top|restrict_apply₀'|ae_restrict_mem₀|measure_biUnion_null_iff|image_iUnion₂|ae_restrict_iff'₀" mathlib/Mathlib`
- `grep -rn "LocallyLipschitzOn.*hausdorff|hausdorffMeasure.*LocallyLipschitz" mathlib/Mathlib simongmt/Poincare (no match)`
- `grep -rn "IsC1Submanifold|IsSimonSubmanifold" simongmt/Poincare --include=*.lean | grep theorem`
- `diff local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean (identical)`
- `python3 over runs/.../dag.json: lean_name and lean_statement of every DAG node (collision check)`
- `lake env lean /tmp/tc-decomp/Check.lean, Glue.lean, Children.lean (statement elaboration, parent glue from stubbed children and siblings, trial child proofs)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-tangent-characterizations-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Data/Set/Lattice/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCompletion.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaSubmanifoldExample.lean`

Snapshot: project d09bc8a (its Contract.lean is byte-identical to the workspace contract), Mathlib 25730c7c, plus the pinned simongmt package.

Reusable declarations found, by child:
- (1) SimonGMT Chapter04: hausdorff_blowUp_image (H^n(eta_{x,r}(S)) = ofReal(r^-1)^n H^n(S) for arbitrary S), blowUpHomeomorph, map_inverse_blowUp_carrier (push-forward of H^n restricted to eta(M) by eta^-1 equals ofReal(r^-1)^n times H^n restricted to M). Mathlib: euclideanHausdorffMeasure_homothety_image, Isometry.euclideanHausdorffMeasure_image, MeasurableEmbedding.integral_map, integral_smul_measure.
- (2) Mathlib: withDensity_apply, withDensity_apply_eq_zero', integral_withDensity_eq_integral_toReal_smul0, Measure.restrict_apply0', ae_restrict_mem0, Integrable.lintegral_lt_top. SimonGMT's RectifiableVarifold.integral_weighted_blowUp is the varifold-specific model of child (2c).
- (3) SimonGMT: Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (arbitrary sets), Chapter02.area_image_null_of_lipschitzOn (single Lipschitz-on-set map only). Mathlib: EuclideanSpace.euclideanHausdorffMeasure_eq_volume, TopologicalSpace.isOpen_biUnion_countable.
- (4) Mathlib: ContDiffAt.exists_lipschitzOnWith (C1 implies locally Lipschitz on open sets), measure_biUnion_null_iff. SimonGMT's IsSimonSubmanifold.nonempty_volumeAtlas is an alternative countable-atlas route.
- Parent glue: SimonGMT countablyRectifiable_of_measure_zero, CountablyRectifiable.mono; Mathlib ae_restrict_iff'0, withDensity_absolutelyContinuous, integrableOn_const.

No match: neither library states the blow-up change of variables for an arbitrary set and integrand, the null-image lemma for maps that are only locally Lipschitz on an open set, or the chartwise a.e. transfer over an IsC1Submanifold cover. These are therefore supplied as children (1), (3) and (4).

Compilation checks: all four child statements elaborate. Trial proofs of all four children compiled (exit 0); child (1) imported Poincare.SimonGMT.Chapter04.WeightedBlowUp, whose oleans are present in .lake/packages/simongmt. The parent compiled from the children together with the stubbed sibling interfaces.

Collision check: no proposed lean_name collides with any lean_name in dag.json.
