# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝᵏ := EuclideanSpace ℝ (Fin k) with Euclidean norm |·| and inner product ⟨·,·⟩; Lⁿ := volume on ℝⁿ; Hⁿ := μHE[n] (Mathlib's Euclidean-normalised n-dimensional Hausdorff measure; on ℝⁿ it equals Lⁿ by Mathlib `EuclideanSpace.euclideanHausdorffMeasure_eq_volume`). A map Ψ is c-antilipschitz on a set S if c|w − w′| ≤ |Ψ(w) − Ψ(w′)| for all w, w′ ∈ S. SimonGMT `CountablyRectifiable n M` (Simon Ch. 3, 1.1) means: there are M₀ ⊆ ℝ^P with Hⁿ(M₀) = 0 and Lipschitz maps F_j : ℝⁿ → ℝ^P (j ∈ ℕ) with M ⊆ M₀ ∪ ⋃_j F_j(ℝⁿ). This lemma is Step 1 of the parent proof: Simon Ch. 3, Lemma 1.2 (“only if”; the printed proof is followed in steps 4–5) together with Remark 1.3 (passage to countably many coordinate patches, done in steps 6–7 with bi-Lipschitz rational balls). The C¹ Approximation Theorem used by the printed proof is Simon Ch. 2, Theorem 1.5; its printed proof is reproduced in step 2.

(N) Null images. If Ψ : ℝⁿ → ℝ^P is Λ-Lipschitz on a set S ⊆ ℝⁿ then Hⁿ(Ψ(S)) ≤ Λⁿ Hⁿ(S) (SimonGMT `Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn`); hence Ψ maps Lⁿ-null subsets of S to Hⁿ-null sets.

1. (Case n = 0.) ℝ⁰ = {0}. Write M ⊆ M₀ ∪ ⋃_j F_j(ℝ⁰) with H⁰(M₀) = 0. Put Φ_j := F_j and Ω_j := ℝ⁰ (open). Every map on the one-point space ℝ⁰ is constant, hence C¹, 0-Lipschitz and 1-antilipschitz (both sides of the antilipschitz inequality are 0). Since M ∖ ⋃_j Φ_j(Ω_j) ⊆ M₀, we get H⁰(M ∖ ⋃_j Φ_j(Ω_j)) = 0. From now on n ≥ 1 (the argument below is also valid for n = 0).

2. (C¹ Approximation Theorem, Simon Ch. 2, 1.5; printed proof.) Claim: if g : ℝⁿ → ℝ is Lipschitz and ε > 0, there are a closed A ⊆ ℝⁿ with Lⁿ(ℝⁿ ∖ A) < ε and h ∈ C¹(ℝⁿ) with h = g on A.
 (a) By Rademacher's theorem (Mathlib `LipschitzWith.ae_differentiableAt`) the set B := {x : g is differentiable at x}, which is Borel (Mathlib `measurableSet_of_differentiableAt`), satisfies Lⁿ(ℝⁿ ∖ B) = 0. The map Dg := fderiv ℝ g : ℝⁿ → L(ℝⁿ, ℝ) is Borel (Mathlib `measurable_fderiv`), and ‖Dg(x)‖ ≤ Lip g for every x.
 (b) (Lusin, also on sets of infinite measure.) For a ≥ 1 let S_a := {x : a − 1 ≤ |x| < a} (bounded Borel annuli). Lusin's theorem for the finite measure Lⁿ⌞(S_a ∩ B) (SimonGMT `Chapter01.exists_isClosed_continuousOn_of_measurable` applied to the n coordinates x ↦ Dg(x)(e_i), intersecting the resulting closed sets) gives a closed C_a ⊆ S_a ∩ B with Dg|C_a continuous and Lⁿ((S_a ∩ B) ∖ C_a) < ε/2^{a+3}. Put C := ⋃_a C_a. Every bounded set meets only finitely many S_a, hence finitely many C_a; so C is closed (locally finite union of closed sets) and Dg|C is continuous (near each point C is a finite union of closed sets on each of which Dg is continuous). Moreover C ⊆ B and Lⁿ(ℝⁿ ∖ C) ≤ Lⁿ(ℝⁿ ∖ B) + Σ_a Lⁿ((S_a ∩ B) ∖ C_a) < ε/2. (The accepted DAG lemma `lpf_c1r_lusin_closed` states exactly this for an arbitrary Borel set S ⊆ ℝⁿ, here S = B.)
 (c) For x, y ∈ C with x ≠ y put R(x,y) := (g(y) − g(x) − Dg(x)(y − x))/|y − x|; then |R(x,y)| ≤ 2 Lip g. For k ≥ 1 and x ∈ C put η_k(x) := sup{|R(x,y)| : y ∈ C, 0 < |y − x| < 1/k} (sup ∅ := 0). For fixed y, x ↦ R(x,y) is continuous on C ∖ {y} (g and Dg|C are continuous). Hence if η_k(x) > t, witnessed by some y, then η_k(x′) > t for all x′ ∈ C sufficiently close to x; so η_k is lower semicontinuous on C, hence Borel. The η_k decrease in k, and η_k(x) → 0 for every x ∈ C because g is differentiable at x ∈ C ⊆ B with derivative Dg(x).
 (d) (Egoroff.) By Egoroff's theorem (Mathlib `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto`) on each finite-measure set C ∩ S_a with tolerance ε/2^{a+3} (applied to the sequence (η_k)_k), there is a measurable A₀ ⊆ C with Lⁿ(C ∖ A₀) < ε/4 such that η_k → 0 uniformly on every bounded subset of A₀ (a bounded set meets only finitely many S_a). By inner regularity of Lⁿ, again annulus by annulus, there is a closed A ⊆ A₀ with Lⁿ(A₀ ∖ A) < ε/4 (the union of the closed pieces is closed by local finiteness). Hence Lⁿ(ℝⁿ ∖ A) < ε/2 + ε/4 + ε/4 = ε. (The accepted DAG lemma `lpf_c1r_egoroff_closed` is this closed-set form of Egoroff's theorem; the accepted DAG lemma `lpf_c1r_uniform_remainder` packages (c)–(d) together with the Whitney condition of (e): for Lipschitz g, closed C on which g is differentiable with Dg|C continuous, and ε > 0, it yields a closed A ⊆ C with Lⁿ(C ∖ A) < ε satisfying that condition.)
 (e) (Whitney.) g|A and Dg|A are continuous. If K ⊆ A is compact and δ > 0, choose k with sup_K η_k < δ (K is bounded); then for x ∈ K and y ∈ A with 0 < |y − x| < 1/k: |g(y) − g(x) − Dg(x)(y − x)| = |R(x,y)| |y − x| ≤ η_k(x)|y − x| ≤ δ|y − x|. This is Whitney's condition (Simon Ch. 2, 1.6(‡)). By Whitney's Extension Theorem (Simon Ch. 2, Theorem 1.6; proof in [EG92, §6.5] or [Fed69, 3.1.14]; in Lean it is the accepted DAG lemma `lpf_c1r_whitney_extension`, whose hypotheses are exactly: A closed, g and Dg continuous on A, and the compact-uniform remainder estimate just proved) there is h ∈ C¹(ℝⁿ) with h = g on A (and Dh = Dg on A). □

3. (Vector-valued version.) Let F : ℝⁿ → ℝ^P be Lipschitz and ε > 0. If P = 0 put G :≡ 0 and A := ℝⁿ. Otherwise apply step 2 to each coordinate F^l := ⟨F, e_l⟩ (Lipschitz), l = 1, …, P, with ε/P, obtaining closed A_l and h_l ∈ C¹(ℝⁿ) with h_l = F^l on A_l; put A := ⋂_l A_l (closed, Lⁿ(ℝⁿ ∖ A) ≤ Σ_l Lⁿ(ℝⁿ ∖ A_l) < ε) and G := Σ_l h_l e_l ∈ C¹(ℝⁿ; ℝ^P). Then F = G on A.

4. (Simon's proof of Lemma 1.2: reduction to C¹ maps.) By hypothesis M ⊆ M₀ ∪ ⋃_{j∈ℕ} F_j(ℝⁿ) with Hⁿ(M₀) = 0 and each F_j Lipschitz. For j ∈ ℕ and i ≥ 1, step 3 gives G_{ij} ∈ C¹(ℝⁿ; ℝ^P) and a closed A_{ij} with F_j = G_{ij} on A_{ij} and Lⁿ(ℝⁿ ∖ A_{ij}) < 1/i. Put Z_j := ℝⁿ ∖ ⋃_i A_{ij}. Then Lⁿ(Z_j) ≤ 1/i for every i, so Lⁿ(Z_j) = 0, and E_j := F_j(Z_j) satisfies Hⁿ(E_j) = 0 by (N). If w ∉ Z_j then w ∈ A_{ij} for some i and F_j(w) = G_{ij}(w). Hence
 (1) M ⊆ M₀ ∪ ⋃_j E_j ∪ ⋃_{i,j} G_{ij}(ℝⁿ).

5. (Critical points have Hⁿ-null image; Simon: “by the area formula …{x : JG_{ij} = 0}…”.) Fix G := G_{ij} and let Crit := {w ∈ ℝⁿ : DG(w) is not injective}. The set of injective linear maps ℝⁿ → ℝ^P is open in L(ℝⁿ, ℝ^P): if A is injective there is m > 0 with |As| ≥ m|s| for all s (finite dimension; any m > 0 works when n = 0), and then every B with ‖B − A‖ < m satisfies |Bs| ≥ (m − ‖B − A‖)|s|, so B is injective. Since DG is continuous, Crit is closed, hence Borel. G is differentiable at every point. By the area formula in the form of SimonGMT `Chapter02.area_image_eq_zero_of_critical` (for a Borel set s on which a map ℝⁿ → ℝ^P is differentiable with non-injective derivative, the Hⁿ-measure of the image of s is 0; here finrank ℝ ℝⁿ = n), Hⁿ(G(Crit)) = 0.

6. (Regular points: bi-Lipschitz balls; inverse-function argument.) Let w₀ ∈ ℝⁿ ∖ Crit and A := DG(w₀). As A is an injective linear map on the finite-dimensional space ℝⁿ, there is m > 0 with |As| ≥ m|s| for all s ∈ ℝⁿ. Put c := m/2. By continuity of DG choose r > 0 with ‖DG(z) − A‖ ≤ c for |z − w₀| < r. For z, z′ in the convex ball B_r(w₀), the mean value inequality applied to z ↦ G(z) − Az gives |G(z) − G(z′) − A(z − z′)| ≤ c|z − z′|, hence |G(z) − G(z′)| ≥ m|z − z′| − c|z − z′| = c|z − z′|; and since ‖DG‖ ≤ ‖A‖ + c on B_r(w₀), the mean value inequality also gives |G(z) − G(z′)| ≤ (‖A‖ + c)|z − z′|. (Accepted DAG lemma `lpf_c1_local_antilipschitz` is the antilipschitz part.) Choose an open ball O with rational centre and rational radius with w₀ ∈ O ⊆ B_r(w₀); G is Lipschitz and c-antilipschitz on O. Let 𝒪_{ij} be the countable set of open balls O with rational centre and rational radius such that G_{ij} is Lipschitz on O (with some constant) and c-antilipschitz on O for some c > 0. We have shown ℝⁿ ∖ Crit_{ij} ⊆ ⋃_{O∈𝒪_{ij}} O, so
 (2) G_{ij}(ℝⁿ) ⊆ G_{ij}(Crit_{ij}) ∪ ⋃_{O∈𝒪_{ij}} G_{ij}(O).

7. (The charts.) Let 𝒯 be the countable set of triples (i, j, O) with i ≥ 1, j ∈ ℕ and O ∈ 𝒪_{ij}. If 𝒯 = ∅ put Φ_k :≡ 0 and Ω_k := ∅ for all k ∈ ℕ (∅ is open, constants are C¹, and the Lipschitz and antilipschitz conditions on ∅ hold vacuously, e.g. with constants 0 and 1). Otherwise choose a surjection k ↦ (i_k, j_k, O_k) from ℕ onto 𝒯 and put Φ_k := G_{i_k j_k}, Ω_k := O_k. In both cases every Ω_k is open, every Φ_k is C¹ on ℝⁿ (`ContDiff ℝ 1`), Lipschitz on Ω_k and antilipschitz on Ω_k with a positive constant, and ⋃_k Φ_k(Ω_k) = ⋃_{(i,j,O)∈𝒯} G_{ij}(O).

8. (Conclusion.) By (1) and (2), M ∖ ⋃_k Φ_k(Ω_k) ⊆ M₀ ∪ ⋃_j E_j ∪ ⋃_{i,j} G_{ij}(Crit_{ij}), a countable union of Hⁿ-null sets (hypothesis, step 4 and step 5). By countable subadditivity Hⁿ(M ∖ ⋃_k Φ_k(Ω_k)) = 0, which together with step 7 is the claim. ∎

Implementation remarks (not part of the mathematical argument). (i) The frozen type of this lemma is byte-identical to that of `lpf_countably_rectifiable_c1_cover` (lipschitz-pushforward branch; speculative-ready, not comparator-accepted at the time of this split, hence the fresh name). If that declaration is comparator-accepted when this node is decomposed, it can be reused as a reuse child with its exact name and identical type. (ii) Otherwise, in this node's own decomposition the following comparator-accepted declarations can be included as reuse children (exact names, identical frozen types): `lpf_c1r_lusin_closed` (step 2(b)), `lpf_c1r_egoroff_closed` (step 2(d)), `lpf_c1r_uniform_remainder` (steps 2(c)–(e), Whitney condition), `lpf_c1r_whitney_extension` (step 2(e)), `lpf_c1_local_antilipschitz` (antilipschitz part of step 6). (iii) Imports: `Poincare.SimonGMT.Chapter02.AreaCritical` (step 5) and `Chapter01.Lusin` are prebuilt in the shared package and may be added to Submission.lean, as accepted nodes do; `Poincare.SimonGMT.Chapter02.WhitneyExtension` is not prebuilt in the read-only shared package, so SimonGMT's `exists_contDiff_one_extension_of_whitney` must not be imported — use `lpf_c1r_whitney_extension` instead.

## Key steps

1. Case n = 0: take Φ_j := F_j and Ω_j := ℝ⁰.
2. C¹ Approximation Theorem (Simon Ch. 2, 1.5, printed proof): Rademacher + Lusin + Egoroff yield a closed A with Lⁿ(ℝⁿ∖A) < ε satisfying Whitney's condition, and Whitney extension gives h ∈ C¹ with h = g on A; apply componentwise for ℝ^P-valued maps.
3. Simon's Lemma 1.2: F_j = G_ij on A_ij, so M ⊆ M₀ ∪ ⋃_j F_j(Z_j) ∪ ⋃_{i,j} G_ij(ℝⁿ) with Lⁿ(Z_j) = 0 and hence Hⁿ(F_j(Z_j)) = 0.
4. The image of the critical set {DG_ij not injective} (closed) is Hⁿ-null by the area formula.
5. At regular points the mean value inequality makes G_ij Lipschitz and antilipschitz on a small rational ball; countably many such balls cover the regular set.
6. Enumerate the triples (i, j, O) as charts (Φ_k, Ω_k) and conclude by countable subadditivity.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch06/Contract.lean workspace GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (both identical; workspace HEAD d8d46c95)`
- `python3 importlib verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') -> scope prefix: open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasWeightedApproximateTangentSpaceAt); open Poincare.SimonGMT.Chapter01 (dimensionalUpperDensity); noncomputable section; end`
- `grep -n 'def CountablyRectifiable|def HasApproximateTangentSpaceAt|def HasWeightedApproximateTangentSpaceAt|theorem HasWeightedApproximateTangentSpaceAt.unique|def blowUpMap' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n '^theorem|^def' simongmt Chapter02/{Lipschitz,AreaLipschitz,AreaCritical,AreaDomain,WhitneyExtension,WhitneyJet}.lean Chapter01/{Lusin,DensityComparison}.lean Chapter03/{SubmanifoldCover,Differential,DisjointCover}.lean`
- `grep -n '^theorem' mathlib/Mathlib/Analysis/Calculus/Rademacher.lean; sed -n 1,200p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, euclideanHausdorffMeasure_smul0)`
- `grep -rn 'theorem Measurable.find|theorem measurable_find|theorem ContinuousOn.measurableEmbedding|theorem MeasurableSet.image_of_continuousOn_injOn|theorem measurable_fderiv|theorem measurableSet_of_differentiableAt|theorem DifferentiableWithinAt.differentiableAt|theorem ae_restrict_iff|theorem tendstoUniformlyOn_of_ae_tendsto|IsSigmaCompact.image|theorem normDet_sq_eq_det_gram|theorem normDet_nonneg|theorem hausdorffMeasure_image_le' mathlib/Mathlib`
- `ls lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02 and Chapter01 (WhitneyExtension.olean absent; AreaCritical, AreaLipschitz, AreaDomain, WhitneyJet, Lusin, DensityComparison present)`
- `python3 scan of dag.json (360 nodes): uniqueness of slicing_im_tg_* names; byte-identity of child types with lpf_countably_rectifiable_c1_cover / lpf_weighted_tangent_on_c1_chart (speculative-ready); live statuses and statements of lpf_c1r_*, lpf_c1_local_antilipschitz, lpf_lipschitz_c1_immersion_pieces, lpf_wtc_*, lpf_tde_chart_directional_deriv, lpf_ccr_hasDerivAt_line_of_comp, rectifiability_weighted_tangent_ae, br_weightedTangent_congr, iwl_weighted_tangent_locality`
- `read nodes/root-lipschitz-pushforward-im-a1/decomposition-v1.json, nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/decomposition-v1.json, nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/decomposition-v1.json, nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/decomposition-v2.json (twin proofs; reuse-child mechanism)`
- `git show <workspace_result_commit>:GMT/Ch06/Submission.lean for 138 accepted nodes (extra SimonGMT imports such as Chapter02.AreaDomain, Chapter01.DensityComparison, Chapter02.AreaBranches are allowed)`
- `lake env lean /tmp/tg_split/Stmts.lean (four child types in exact comparator scope; 0 errors)`
- `lake env lean /tmp/tg_split/Assembly.lean (frozen parent type proved from chart_cover, chart_tangent, chart_gradient stubs; #print axioms: propext, sorryAx [stubs only], Classical.choice, Quot.sound)`
- `lake env lean /tmp/tg_split/CProof.lean (complete proof of the line_deriv frozen type; axioms propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/tg_split/Avail.lean (#check of cited Mathlib and SimonGMT lemmas in the Submission import closure)`
- `python3 verifier/lean_contract.py validate_lean_statement on the four child types (all OK)`
- `rg 'slicing_im_tg' local-references/197bdd4b88278494/project and lake-packages-25730c7c/simongmt (no match)`
- `sed book/chapter-03.txt (1.1-1.9, 2.1-2.2), chapter-02.txt (1.4-1.8, 4.1-4.11), chapter-01.txt (3.6-3.7)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/decomposition-v2.json`
- `/tmp/tg_split/Stmts.lean`
- `/tmp/tg_split/Assembly.lean`
- `/tmp/tg_split/CProof.lean`
- `/tmp/tg_split/Avail.lean`

Snapshot and imports:
- The snapshot (project d8d46c95, the workspace HEAD; Mathlib 25730c7c) contains the frozen Ch06 contract, byte-identical to the workspace Contract.lean and Submission.lean. Child types may therefore use only contract, SimonGMT and Mathlib names. The comparator scope is namespace GMT.Ch06 with the contract's opens.
- SimonGMT supplies the following:
  - CountablyRectifiable as countably many Lipschitz images plus an Hⁿ-null set, and HasWeightedApproximateTangentSpaceAt with uniqueness at θ(x) ≠ 0.
  - Lipschitz image bounds for μHE[n].
  - Area-formula critical-image and injective results (AreaCritical, AreaLipschitz, AreaDomain), Lusin (Chapter01.Lusin) and the upper density theorem 3.6 (Chapter01.DensityComparison). These modules are not imported by the contract but are prebuilt and may be added to the imports, as accepted nodes do.
  - Its Chapter02.WhitneyExtension module is not prebuilt, so it cannot be imported.
- SimonGMT lacks the chart-cover direction of Simon Lemma 1.2 (SubmanifoldCover proves only the easy direction), a tangential gradient for Lipschitz functions, and tangent identification on C¹ charts.
- Mathlib supplies Rademacher on sets (LipschitzOnWith.ae_differentiableWithinAt_of_mem), μHE[n] = volume on ℝⁿ, measurable_fderiv, measurableSet_of_differentiableAt, Lusin–Souslin images and measurable embeddings, Measurable.find, Egorov, and normDet_sq_eq_det_gram.

DAG and reuse:
- The chart-cover and chart-tangent lemmas exist in the DAG only as the speculative-ready lpf twins. Their types are byte-identical to the children chart_cover and chart_tangent, but they are not yet comparator-accepted, so fresh names are used.
- Many of the twins' leaves are comparator-accepted and are listed in the child proofs for reuse in those children's own decompositions.
- No accepted declaration has a type identical to any child. slicing_im_tg_* matches nowhere: not in the snapshot project, not in SimonGMT, not among the 360 DAG nodes.

Kernel checks:
- All four child types elaborate in the exact scope and pass the verifier's statement validator.
- The frozen parent type is proved from chart_cover, chart_tangent and chart_gradient; sorryAx comes only from the stubs.
- line_deriv is fully proved with standard axioms.

These checks do not certify the analytic proofs of chart_cover, chart_tangent and chart_gradient.
