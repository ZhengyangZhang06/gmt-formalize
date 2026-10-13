# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^k = Eucl k with Euclidean norm |·|; Lⁿ = volume on ℝⁿ; Hⁿ = μHE[n], which equals Lⁿ on ℝⁿ (`EuclideanSpace.euclideanHausdorffMeasure_eq_volume`). DF(x) := fderiv ℝ F x. A map Φ is c-antilipschitz on Ω if c|w − w′| ≤ |Φ(w) − Φ(w′)| for all w, w′ ∈ Ω. For v ∈ ℝ^P and l ∈ Fin P, v l = ⟨v, e_l⟩ is the l-th coordinate, and |v l − v' l| ≤ |v − v'|.
This is Simon Ch. 3, Lemma 1.2, “only if” part, with its printed argument: the C¹ Approximation Theorem applied to the Lipschitz parametrizations, the area formula for the critical set, and local C¹ embeddings near points of injective differential. The charts are localized to small balls, as in Remark 1.3, so that every chart is both Lipschitz and antilipschitz. Ingredients:
- the sibling lemma c1_approx (Simon Ch. 2, Theorem 1.5): for a K-Lipschitz u : ℝⁿ → ℝ and ε ∈ (0, ∞] there are a closed A with Lⁿ(ℝⁿ ∖ A) < ε and a C¹ h with u = h on A and HasFDerivAt u (Dh(x)) x for x ∈ A;
- SimonGMT `Poincare.SimonGMT.Chapter02.area_image_criticalSet_eq_zero`: for any F : ℝⁿ → ℝ^P, Hⁿ(F({x : F differentiable at x, DF(x) not injective})) = 0 (Simon Ch. 2, area formula: the Jacobian vanishes there);
- SimonGMT `Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn`: if F is Λ-Lipschitz on S, then Hⁿ(F(S)) ≤ Λⁿ Hⁿ(S).

1. (Lipschitz parametrizations.) By definition of CountablyRectifiable n M there are M₀ with Hⁿ(M₀) = 0 and maps F_j : ℝⁿ → ℝ^P (j ∈ ℕ), F_j Λ_j-Lipschitz, with M ⊆ M₀ ∪ ⋃_j F_j(ℝⁿ).

2. (Vector-valued C¹ approximation.) Fix j and k ∈ ℕ. For l ∈ Fin P the coordinate x ↦ F_j(x) l is Λ_j-Lipschitz. Apply c1_approx to it with ε := ((k+1)(P+1))⁻¹. This gives a closed A_{j,k,l} with Lⁿ(ℝⁿ ∖ A_{j,k,l}) < ε and a C¹ h_{j,k,l} : ℝⁿ → ℝ such that, for x ∈ A_{j,k,l}, F_j(x) l = h_{j,k,l}(x) and x ↦ F_j(x) l has derivative Dh_{j,k,l}(x) at x.
 - Put A_{j,k} := ⋂_{l} A_{j,k,l}, closed (A_{j,k} = ℝⁿ if P = 0), with Lⁿ(ℝⁿ ∖ A_{j,k}) ≤ P·ε < (k+1)⁻¹.
 - Define G_{j,k} : ℝⁿ → ℝ^P by G_{j,k}(x) l := h_{j,k,l}(x), i.e. G_{j,k} = (EuclideanSpace.equiv (Fin P) ℝ).symm ∘ (x ↦ (l ↦ h_{j,k,l}(x))). It is C¹ because all coordinates are (`contDiff_pi` composed with a continuous linear equivalence).
 - For x ∈ A_{j,k}: F_j(x) = G_{j,k}(x), since all coordinates agree. Also F_j is differentiable at x with DF_j(x) = DG_{j,k}(x). A map into ℝ^P has derivative T at x iff each coordinate x ↦ F(x) l has derivative (v ↦ T(v) l); the l-th coordinate of DG_{j,k}(x) is Dh_{j,k,l}(x).

3. (Two null images.)
 (a) N_j := ℝⁿ ∖ ⋃_k A_{j,k} has Lⁿ(N_j) ≤ Lⁿ(ℝⁿ ∖ A_{j,k}) < (k+1)⁻¹ for every k, so Lⁿ(N_j) = 0. As F_j is Λ_j-Lipschitz, Hⁿ(F_j(N_j)) ≤ Λ_jⁿ Hⁿ(N_j) = Λ_jⁿ Lⁿ(N_j) = 0.
 (b) Crit_j := {x : F_j differentiable at x and DF_j(x) not injective} has Hⁿ(F_j(Crit_j)) = 0 by area_image_criticalSet_eq_zero.

4. (Local charts at regular points.) Let R_{j,k} := {x ∈ A_{j,k} : DG_{j,k}(x) injective}. Fix x ∈ R_{j,k} and write G := G_{j,k}, T := DG(x).
 - As T is injective on the finite-dimensional ℝⁿ, there is a > 0 with |T u| ≥ 2a|u| for all u (the minimum of |Tu| on the unit sphere is positive).
 - DG is continuous, so there is r > 0 with ‖DG(z) − T‖ ≤ a for |z − x| < r. Put B := B(x, r), which is open and convex.
 - Mean value inequality for z ↦ G(z) − T z on B (derivative DG(z) − T of norm ≤ a): |G(z) − G(z′) − T(z − z′)| ≤ a|z − z′| for z, z′ ∈ B. Hence |G(z) − G(z′)| ≥ 2a|z − z′| − a|z − z′| = a|z − z′|, i.e. G is a-antilipschitz on B. Also |G(z) − G(z′)| ≤ (‖T‖ + a)|z − z′|, i.e. G is Lipschitz on B.
 (The antilipschitz part is the comparator-accepted DAG lemma lpf_c1_local_antilipschitz, which a decomposition of this node may reuse with its identical type.)
 By Lindelöf (ℝⁿ is second countable; `TopologicalSpace.isOpen_iUnion_countable`) there are countably many such balls B_{j,k,p} (p ∈ ℕ) with R_{j,k} ⊆ ⋃_p B_{j,k,p}. Pad with B_{j,k,p} := ∅ if R_{j,k} = ∅.

5. (The charts.) Enumerate ℕ³ ∋ (j,k,p) by ℕ, e.g. i ↦ (Nat.unpair i).1 and Nat.unpair (Nat.unpair i).2. Set Φ_i := G_{j,k} and Ω_i := B_{j,k,p}. Each Ω_i is open, Φ_i is C¹ (`ContDiff ℝ 1`), and by step 4 Φ_i is Lipschitz and antilipschitz with a positive constant on Ω_i. Empty Ω_i satisfy both conditions vacuously, e.g. with c := 1.

6. (Coverage.) Let y ∈ M ∖ ⋃_i Φ_i(Ω_i). We show that y lies in M₀ ∪ ⋃_j F_j(N_j) ∪ ⋃_j F_j(Crit_j).
 - If y ∉ M₀, then y = F_j(x) for some j and x.
 - If x ∈ N_j we are done. Otherwise x ∈ A_{j,k} for some k, so F_j is differentiable at x with DF_j(x) = DG_{j,k}(x) (step 2).
 - If DG_{j,k}(x) is injective, then x ∈ R_{j,k} ⊆ ⋃_p B_{j,k,p}. Hence y = F_j(x) = G_{j,k}(x) ∈ Φ_i(Ω_i) for the corresponding i, which is impossible.
 - So DF_j(x) is not injective, and x ∈ Crit_j.
 By step 3 and Hⁿ(M₀) = 0, this countable union is Hⁿ-null. Hence Hⁿ(M ∖ ⋃_i Φ_i(Ω_i)) = 0 (`measure_mono_null`, `measure_iUnion_null`). ∎
 (If n > P every subset of ℝ^P is Hⁿ-null and the claim is immediate, but the argument above does not need this case distinction.)

## Key steps

1. Write M ⊆ M₀ ∪ ⋃_j F_j(ℝⁿ) with F_j Lipschitz.
2. Apply c1_approx to each coordinate of F_j with ε = ((k+1)(P+1))⁻¹; intersect to get closed A_{j,k} (Lⁿ(A_{j,k}ᶜ) < 1/(k+1)) and C¹ G_{j,k} with F_j = G_{j,k}, DF_j = DG_{j,k} on A_{j,k}.
3. F_j(ℝⁿ ∖ ⋃_k A_{j,k}) is null (Lipschitz image of a null set); F_j(critical set) is null (SimonGMT area_image_criticalSet_eq_zero).
4. At points of A_{j,k} where DG_{j,k} is injective, small balls make G_{j,k} Lipschitz and antilipschitz (mean value inequality); Lindelöf gives countably many such charts.
5. Every point of M outside the charts lies in M₀ or in one of the two null images.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean (byte-identical); read Contract.lean (IsRectifiableTriple, Eucl, scope commands)`
- `grep -rn 'slicing_im_coarea_' local-references/197bdd4b88278494/project (no match)`
- `python3 scan of dag.json: statuses and lean_statement of all lipschitz_pushforward nodes; byte comparison of candidate child types with lpf_c1_approximation_real, lpf_countably_rectifiable_c1_cover, lpf_weighted_tangent_on_c1_chart (identical, all speculative-ready) and lpf_ccr_hasDerivAt_line_of_comp (accepted 18:04Z, Eucl Q-valued); collision check of the nine names against all 369 DAG lean_name values (none)`
- `read nodes/root-lipschitz-pushforward-im-a1-{countably-rectifiable-c1-cover-a1,weighted-tangent-on-c1-chart-a1,lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1,chart-chain-rule-a1-line-deriv-comp-a1}/parent-supplied-natural-proof.md and nodes/root-slicing-a1-slice-integer-multiplicity-a1/{parent-supplied-natural-proof.md,decomposition-v1.json}`
- `grep -n '^theorem|^def' SimonGMT Chapter03/{Rectifiable,Differential,DisjointCover,SubmanifoldCover}.lean and Chapter02/{AreaLipschitz,AreaDomain,AreaCritical,Area,Lipschitz,CoareaLinear,CoareaProjection,WhitneyExtension}.lean`
- `grep for SimonGMT names weighted_area_formula_lipschitzOn_fiberSum, weighted_area_formula_lipschitz_injOn, injective_area_formula_lipschitzOn, area_image_criticalSet_eq_zero, euclideanHausdorffMeasure_image_le_of_lipschitzOn, exists_contDiff_one_extension_of_whitney, exists_isClosed_continuousOn_of_measurable, simon_theorem_3_6, coarea_projection_lintegral (all present)`
- `grep in pinned Mathlib for hausdorffMeasure_apply, hausdorffMeasure_le_liminf_tsum, euclideanHausdorffMeasure_def, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero, normDet_comp_of_finrank_eq, normDet_eq_abs_det, normDet_codRestrict, lintegral_image_eq_lintegral_abs_det_fderiv_mul, OpenPartialHomeomorph.contDiffAt_symm, measurePreserving_piFinSuccAbove, PiLp.volume_preserving_ofLp, Measurable.lintegral_prod_right', MeasurableSet.image_of_continuousOn_injOn, NullMeasurableSet.exists_measurable_subset_ae_eq, Measure.restrict_apply₀', restrict_congr_set, lintegral_iUnion, lintegral_tsum, lintegral_inter_add_sdiff, LipschitzOnWith.extend_real, isOpen_iUnion_countable (all present)`
- `sed book/chapter-02.txt §6 (6.1–6.7) and book/chapter-03.txt §1–2 (1.1–1.9, 2.1–2.10)`
- `lake build GMT.Ch06.Submission in scratch /tmp/coarea-decomp-47PgtZ/proj (frozen d8d46c9 contract, shared lake-packages-25730c7c)`
- `lake env lean Scratch/Stmts.lean and Scratch/FinalCheck.lean (nine child types and the parent type in the exact comparator scope; 0 errors)`
- `lake env lean Scratch/Assembly.lean (parent type from eilenberg, glue, pieces, chart_critical, chart_regular; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean Scratch/Pieces.lean (pieces from c1_approx, chart_cover, chart_tangent, line_deriv; standard axioms) and Scratch/GradId.lean`
- `lake env lean Scratch/Glue.lean (glue proved outright; standard axioms); lake env lean Scratch/Review_C1.lean (c1_approx from the accepted lpf_c1r_lusin_closed, lpf_c1r_uniform_remainder, lpf_c1r_whitney_extension types; standard axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1-line-deriv-comp-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/Stmts.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/FinalCheck.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/Assembly.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/Pieces.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/Glue.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/GradId.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/Review_C1.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract. Submission is byte-identical to it, and no `slicing_im_coarea_*` name exists in the project or in the 369 DAG nodes. SimonGMT supplies the needed area-formula library: weighted_area_formula_lipschitzOn_fiberSum, injective_area_formula_lipschitzOn, area_image_criticalSet_eq_zero, euclideanHausdorffMeasure_image_le_of_lipschitzOn, a Whitney extension (source only, no .olean), Lusin, the upper density theorem, the linear co-area formula and HasWeightedApproximateTangentSpaceAt with uniqueness. It has no nonlinear co-area formula and no Eilenberg inequality. Mathlib supplies the Hausdorff measure covering lemmas, the μHE normalization, normDet, the inverse function theorem, change of variables, Fubini/Tonelli and Lusin–Souslin. The lipschitz-pushforward branch has speculative-ready nodes byte-identical to three proposed children (c1_approx, chart_cover, chart_tangent); because they are not accepted, they get new names here, and their accepted sub-lemmas (lpf_c1r_*, lpf_wtc_*, lpf_c1_local_antilipschitz, lpf_raf_chart_change_of_variables) are cited for reuse at the next level. lpf_ccr_hasDerivAt_line_of_comp was accepted during this session and is cited as an alternative route for line_deriv. Lean checks in the exact comparator scope: all nine child types elaborate; the parent type follows from five children; pieces follows from four; glue is proved outright; c1_approx follows from three accepted types. All of these use only propext, Classical.choice and Quot.sound. These checks do not certify the remaining analytic proofs.
