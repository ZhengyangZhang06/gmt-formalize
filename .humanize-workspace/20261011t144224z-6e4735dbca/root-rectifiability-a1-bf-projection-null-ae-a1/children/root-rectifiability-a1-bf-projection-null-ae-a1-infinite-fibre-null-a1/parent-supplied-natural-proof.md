# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1.bf_projection_null_ae-a1`
- Child DAG node: `root.rectifiability-a1.bf_projection_null_ae-a1.infinite_fibre_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the fibre-counting half of Eilenberg's inequality (Simon, Ch. 2, 1.8(ii); Federer 2.10.25; Lemma 2.3 of Hovila–Järvenpää–Järvenpää–Ledrappier, Geom. Dedicata 161 (2012)), specialised to the finiteness of almost every fibre. It is extracted from step 3(c) of the parent proof, with two changes. Fatou's lemma replaces monotone convergence, so neither the nesting of dyadic cubes nor the identity sup_i N_i = #fibre is needed. Measurable hulls replace σ-compactness of the pieces, so a Borel E suffices.

Notation. k := m + 1 ≥ 1. A point x of ℝ^N = Eucl N has coordinates x_j = x j for j ∈ Fin N; ℝᵏ = Eucl k. Hᵏ := μHE[k] on ℝ^N and Lᵏ := volume on ℝᵏ. Measures are evaluated on arbitrary sets as outer measures, which are monotone and countably subadditive; [0,∞] = ℝ≥0∞. The hypotheses are: E is Borel, Hᵏ(E) < ∞, and f is K-Lipschitz with K ∈ ℝ≥0. Put Y := {y ∈ ℝᵏ : E ∩ f⁻¹({y}) is infinite}. We must show Lᵏ(Y) = 0.

1. Two library facts.
 (a) On ℝᵏ, μHE[k] = Lᵏ. This is Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume k; Eucl k is EuclideanSpace ℝ (Fin k).
 (b) For every S ⊆ ℝ^N, Lᵏ(f(S)) ≤ K^k·Hᵏ(S). Indeed f is K-Lipschitz on S (LipschitzWith.lipschitzOnWith). SimonGMT Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn k then gives μHE[k](f(S)) ≤ (K:[0,∞])^k·μHE[k](S). Finally (a) rewrites the left side as Lᵏ(f(S)).

2. Dyadic cubes. For i ∈ ℕ let g_i : ℝ^N → ℤ^N (ℤ^N := Fin N → ℤ) be g_i(x) := (⌊2^i·x_j⌋)_{j ∈ Fin N}. For z ∈ ℤ^N let Q_i(z) := g_i⁻¹({z}) = {x : z_j ≤ 2^i·x_j < z_j + 1 for every j}.
 (a) For fixed i, the sets Q_i(z) (z ∈ ℤ^N) are pairwise disjoint, being preimages of distinct values of the function g_i. Moreover x ∈ Q_i(g_i(x)) for every x. The index set ℤ^N is countable.
 (b) Each Q_i(z) is Borel. It is the intersection, over the finitely many j, of the preimages of the interval [z_j, z_j + 1) under the continuous maps x ↦ 2^i·x_j. Alternatively, g_i is measurable by Mathlib Int.measurable_floor (module Mathlib.MeasureTheory.Function.Floor), and singletons of ℤ^N are measurable.
 (c) Separation. Let x, x′ ∈ ℝ^N and j ∈ Fin N with 1 ≤ 2^i·|x_j − x′_j|. Then g_i(x) ≠ g_i(x′). Otherwise ⌊2^i x_j⌋ = ⌊2^i x′_j⌋, and Int.abs_sub_lt_one_of_floor_eq_floor gives 2^i|x_j − x′_j| = |2^i x_j − 2^i x′_j| < 1, a contradiction.
 (d) Eventual separation. Let x ≠ x′. A point of ℝ^N is determined by its coordinates (ext), so there is j with c := |x_j − x′_j| > 0. Since 2^i → ∞ and i ↦ 2^i is monotone, there is i₀ with 2^i·c ≥ 1 for all i ≥ i₀. By (c), g_i(x) ≠ g_i(x′) for all i ≥ i₀; that is, ∀ᶠ i in atTop, g_i(x) ≠ g_i(x′).

3. Splitting Hᵏ(E). For every i, Σ_{z∈ℤ^N} Hᵏ(E ∩ Q_i(z)) = Hᵏ(E). The sets E ∩ Q_i(z), z ∈ ℤ^N, are countably many. They are Borel (E is Borel, and 2(b)), pairwise disjoint (2(a)), and their union is E (2(a)). Countable additivity of the measure Hᵏ (Mathlib measure_iUnion) gives the identity.

4. Counting functions and their integrals. Fix i.
 (a) For z ∈ ℤ^N put A_i(z) := f(E ∩ Q_i(z)) ⊆ ℝᵏ and B_i(z) := toMeasurable Lᵏ (A_i(z)). Then B_i(z) is Borel, A_i(z) ⊆ B_i(z), and Lᵏ(B_i(z)) = Lᵏ(A_i(z)) (Mathlib measurableSet_toMeasurable, subset_toMeasurable, measure_toMeasurable).
 (b) Define N_i : ℝᵏ → [0,∞] by N_i(y) := Σ_{z∈ℤ^N} 1_{B_i(z)}(y), the tsum of the indicator functions (B_i z).indicator 1. Each summand is Borel measurable, hence so is N_i, as a countable sum of measurable [0,∞]-valued functions (Measurable.ennreal_tsum, or Measurable.tsum).
 (c) We have ∫ N_i dLᵏ = Σ_z Lᵏ(B_i(z)) = Σ_z Lᵏ(A_i(z)) ≤ Σ_z K^k·Hᵏ(E ∩ Q_i(z)) = K^k·Σ_z Hᵏ(E ∩ Q_i(z)) = K^k·Hᵏ(E). The first equality is the monotone convergence theorem for series (lintegral_tsum) together with ∫ 1_B dLᵏ = Lᵏ(B) for Borel B (lintegral_indicator_one). The second is (a). The inequality is 1(b) with S := E ∩ Q_i(z), applied termwise (ENNReal.tsum_le_tsum). The next equality is ENNReal.tsum_mul_left, and the last is step 3.
 (d) Put C := K^k·Hᵏ(E). Since (K:[0,∞])^k < ∞ and Hᵏ(E) < ∞, C < ∞. By (c), ∫ N_i dLᵏ ≤ C for every i.

5. Large counts on infinite fibres. Let y ∈ Y and M ∈ ℕ. We claim that N_i(y) ≥ M for all sufficiently large i.
 (a) The fibre E ∩ f⁻¹({y}) is infinite, so it contains a finite set T with exactly M elements (Set.Infinite.exists_subset_card_eq).
 (b) For each of the finitely many pairs (x, x′) ∈ T × T, step 2(d) gives ∀ᶠ i, (x ≠ x′ → g_i(x) ≠ g_i(x′)). A finite conjunction of eventually-true statements is eventually true (Filter.eventually_all_finset over T ×ˢ T). Hence there is i₀ such that g_i is injective on T for every i ≥ i₀.
 (c) Fix i ≥ i₀. Every x ∈ T satisfies x ∈ E, f(x) = y and x ∈ Q_i(g_i(x)). Hence y ∈ f(E ∩ Q_i(g_i(x))) = A_i(g_i(x)) ⊆ B_i(g_i(x)), so 1_{B_i(g_i(x))}(y) = 1.
 (d) The image Z := g_i(T) ⊆ ℤ^N is finite with #Z = #T = M (Finset.card_image_of_injOn), and by (c) 1_{B_i(z)}(y) = 1 for every z ∈ Z. All terms of the series N_i(y) are nonnegative, so N_i(y) is at least its finite partial sum over Z (ENNReal.sum_le_tsum): N_i(y) ≥ Σ_{z∈Z} 1_{B_i(z)}(y) = Σ_{z∈Z} 1 = #Z = M.
 (e) Hence, for every y ∈ Y and every M ∈ ℕ, M ≤ N_i(y) for all large i. So M ≤ liminf_{i→∞} N_i(y) (Filter.le_liminf_of_le; the coboundedness side condition is automatic in the complete lattice [0,∞]). M ∈ ℕ is arbitrary and sup_M M = ∞ in [0,∞] (ENNReal.iSup_natCast). Therefore liminf_{i→∞} N_i(y) = ∞ for every y ∈ Y.

6. Fatou's lemma. Let F(y) := liminf_{i→∞} N_i(y). F is Borel measurable (Measurable.liminf). By Fatou's lemma (lintegral_liminf_le) and step 4(d), ∫ F dLᵏ ≤ liminf_{i→∞} ∫ N_i dLᵏ ≤ C < ∞. The second inequality holds because a liminf of a sequence bounded above by C is ≤ C (e.g. Filter.liminf_le_of_frequently_le' with Filter.Frequently.of_forall). A measurable [0,∞]-valued function with finite integral is finite almost everywhere (ae_lt_top). Hence Lᵏ({y : F(y) = ∞}) = 0.

7. Conclusion. By step 5(e), Y ⊆ {y : F(y) = ∞}. By monotonicity of Lᵏ (measure_mono_null), Lᵏ(Y) = 0. That is, volume {y | (E ∩ f ⁻¹' {y}).Infinite} = 0. ∎

## Key steps

1. On ℝᵏ, μHE[k] equals volume. With the SimonGMT Lipschitz image bound this gives Lᵏ(f(S)) ≤ K^k·Hᵏ(S) for every S ⊆ ℝ^N.
2. The dyadic cubes Q_i(z) = g_i⁻¹{z}, with g_i(x) = (⌊2^i x_j⌋)_j, form a countable Borel partition of ℝ^N at each level i. Two distinct points lie in distinct level-i cubes for all large i, by the floor estimate |a − b| < 1 when ⌊a⌋ = ⌊b⌋.
3. Countable additivity gives Σ_z Hᵏ(E ∩ Q_i(z)) = Hᵏ(E).
4. Take Borel hulls B_i(z) ⊇ f(E ∩ Q_i(z)) of equal Lebesgue measure. Then N_i := Σ_z 1_{B_i(z)} is measurable and ∫N_i dLᵏ ≤ K^k·Hᵏ(E) =: C < ∞.
5. If the fibre over y is infinite, then for every M, N_i(y) ≥ M for all large i, because M fibre points eventually occupy M distinct cubes. Hence liminf_i N_i(y) = ∞.
6. Fatou gives ∫ liminf_i N_i dLᵏ ≤ C < ∞, so liminf_i N_i < ∞ almost everywhere. Hence the infinite-fibre set is Lᵏ-null.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `git archive d8d46c9 | tar -x -C /tmp/bfpn_scratch; cmp /tmp/bfpn_scratch/GMT/Ch06/Submission.lean workspaces/gmt-ch06/GMT/Ch06/Submission.lean (identical)`
- `python3 read of nodes/root-rectifiability-a1-bf-projection-null-ae-a1/parent-child-handoff.json, parent-supplied-natural-proof.md, parent-supplied-plan.md`
- `python3 listing of nodes/root-rectifiability-a1/decomposition-v1.json and decomposition-v2.json subproblems (frozen sibling types of bf_cone_density, bf_trichotomy, density_comparison)`
- `python3 scan of dag.json and nodes/*/decomposition-v*.json lean_name values (rectifiability_bf_infinite_fibre_null: no match; lpf_lli_inner_compact_approx: accepted node root.lipschitz_pushforward_im-a1.locally_lipschitz_image-a1.inner_compact_approx-a1, candidate d24e9e7b; title, statement and lean_statement equal to its handoff)`
- `git show --stat d24e9e7b54d326f9d566fb5543e6cdea196355d1 (Prove lpf_lli_inner_compact_approx)`
- `python3 read of nodes/root-lipschitz-pushforward-im-a1-locally-lipschitz-image-a1-inner-com-6be04fd41f/parent-child-handoff.json (accepted proof and audit)`
- `python3 count of dag.json nodes (195 at 01:57, 197 at 02:21) and max_nodes in swarm-project.json and all .humanize/swarm-configs/*.json (200)`
- `sed /runtime/flows/gmt-claude-8e94f3625cb4/_recursive_lean/runtime.py 945-1120, 1380-1600, 1793-1960, 4274-4360, 6498-6538; github_runtime.py 191-330, 777-790; parallel.py 60-137 (node bound, accepted-name reuse, reused-child publication)`
- `grep -n 'theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn' simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean; grep -n 'def PurelyUnrectifiable|def CountablyRectifiable' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'notation "μHE\["|euclideanHausdorffMeasure_eq_volume' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -rn 'measurable_floor' mathlib/Mathlib/MeasureTheory/Function/Floor.lean; grep -n 'InnerRegularCompactLTTop' mathlib/Mathlib/MeasureTheory/Measure/Regular.lean mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `lake build GMT.Ch06.Submission (scratch /tmp/bfpn_scratch, frozen commit d8d46c9, pinned lake-packages-25730c7c; success)`
- `python3 -I /tmp/bfpn_tools/gen.py: verifier gmt-compare.py child_modules (contract mode) -> Scratch/Ch_parent.lean, Ch_reuse.lean, Ch_eilenberg.lean; lake env lean on each (only 'declaration uses sorry')`
- `lake env lean Scratch/Glue1.lean (σ-compact Borel core from the reused type; ∃ K, LipschitzWith K L_v; #check lintegral_liminf_le, ae_lt_top, lintegral_tsum, lintegral_indicator_one, toMeasurable lemmas, Int.abs_sub_lt_one_of_floor_eq_floor, Set.Infinite.exists_subset_card_eq, Filter.eventually_all_finset, Finset.card_image_of_injOn, ENNReal.sum_le_tsum, measure_iUnion, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, euclideanHausdorffMeasure_image_le_of_lipschitzOn)`
- `lake env lean Scratch/Names2.lean (#check ENNReal.iSup_natCast, Measurable.liminf, measure_mono_null, ENNReal.tsum_mul_left, ENNReal.tsum_le_tsum, LipschitzWith.lipschitzOnWith, ae_all_iff, Measure.restrict_apply', PurelyUnrectifiable.mono, isSigmaCompact_iUnion_of_isCompact, measurableSet_Ico; EuclideanSpace coordinate ext)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-bf-projection-null-ae-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-bf-projection-null-ae-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-locally-lipschitz-image-a1-inner-com-6be04fd41f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/swarm-configs/557a8bd5919a409fb101d7854de51cef.json`
- `/runtime/flows/gmt-claude-8e94f3625cb4/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-8e94f3625cb4/_recursive_lean/github_runtime.py`
- `/runtime/flows/gmt-claude-8e94f3625cb4/_recursive_lean/parallel.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Function/Floor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/tmp/bfpn_scratch/Scratch/Ch_parent.lean`
- `/tmp/bfpn_scratch/Scratch/Ch_reuse.lean`
- `/tmp/bfpn_scratch/Scratch/Ch_eilenberg.lean`
- `/tmp/bfpn_scratch/Scratch/Glue1.lean`
- `/tmp/bfpn_scratch/Scratch/Names2.lean`
- `/tmp/bfpn_tools/gen.py`

The frozen Submission at d8d46c9 is byte-identical to the workspace copy.

Pinned libraries. Pinned Mathlib and SimonGMT supply everything the split and the new child need:
- μHE[k] = volume on Eucl k (EuclideanSpace.euclideanHausdorffMeasure_eq_volume);
- the Lipschitz image bound for μHE (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn);
- toMeasurable hulls, lintegral_tsum, lintegral_indicator_one, measure_iUnion and the floor estimate Int.abs_sub_lt_one_of_floor_eq_floor;
- Set.Infinite.exists_subset_card_eq, Filter.eventually_all_finset and Finset.card_image_of_injOn;
- Fatou (lintegral_liminf_le), ae_lt_top and ENNReal.iSup_natCast;
- Int.measurable_floor, which exists but lives in Mathlib.MeasureTheory.Function.Floor, outside the Submission import closure; the proof also gives an Ico-preimage route.
Neither library has an Eilenberg/fibre-finiteness theorem.

Reuse. The DAG already holds the comparator-accepted Submission.lpf_lli_inner_compact_approx (accepted, candidate d24e9e7b), whose frozen type is exactly the parent's step-1 inner compact approximation. Its title, statement and type are reused verbatim. The controller code maps a reused accepted name to the existing node, so it needs no new node, and the normal publication path skips reused accepted theorems.

Budget. dag.json holds 197 of max_nodes = 200, and this split needs exactly one new node, rectifiability_bf_infinite_fibre_null. That name is unused.

Scratch checks (frozen commit, pinned packages). The parent type, the reused type and the new type all elaborate in the comparator's exact child scope, generated by gmt-compare.py child_modules in contract mode, with only the expected sorry warning. Lean also accepts two pieces of parent glue: the σ-compact Borel core from the reused type, and the Lipschitz property of L_v.
