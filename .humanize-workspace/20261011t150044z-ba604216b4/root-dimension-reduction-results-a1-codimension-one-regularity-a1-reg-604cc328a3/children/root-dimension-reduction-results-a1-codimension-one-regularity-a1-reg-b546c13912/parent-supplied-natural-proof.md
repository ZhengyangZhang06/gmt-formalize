# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_cover-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_cover-a1.regular_ball_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon Ch. 3, Lemma 1.2, 'only if' part (chapter-03.txt lines 39–65 within the lemma at lines 25–66), final paragraph (lines 61–65), as expanded in steps 4, 6 and 7 of the parent proof. Here it is stated for a single C¹ map G; the book's G is G_{ij}.
The printed text makes three claims:
- By the area formula, the image of the zero set of the Jacobian is null.
- At a point x where the Jacobian is non-zero, there is ρ > 0 such that G(B_ρ(x)) is an n-dimensional C¹ submanifold.
- So the image is a null set together with countably many such submanifolds.
Corrections to the printed proof, as in the parent proof:
- The garbled 'by the area formula L^n({x : J_{G_{ij}} = 0}' should read H^n(G_{ij}({J_{G_{ij}} = 0})) = 0.
- The local pieces are submanifolds of ℝ^{n+ℓ} = ℝ^P; the book prints ℝ^n.
As in the parent proof:
- Each local piece is recorded quantitatively by a lower Lipschitz bound on an open ball.
- The countable (Lindelöf) selection uses balls with centres in a dense sequence and radii 1/(p + 1).
Notation: H^n = μHE[n]; B_ρ(x) is the open ball, empty when ρ ≤ 0.

1. (The critical image is null.) Let C := {x ∈ ℝ^n : DG(x) is not injective}.
- G is C¹, hence differentiable everywhere. So C = {x : G is differentiable at x and DG(x) is not injective}.
- This is exactly the set where the Jacobian J_G(x) = √det(DG(x)* DG(x)) vanishes. By the area formula, H^n(G(C)) = 0. In detail:
  - If n > P, then H^n vanishes identically on ℝ^P, so there is nothing to prove.
  - Let n ≤ P. The injective linear maps ℝ^n → ℝ^P form an open set and DG is continuous, so C is closed.
  - Fix R ∈ ℕ and put A_R := C ∩ closedBall(0, R), a compact and hence Lebesgue-measurable set. G is C¹, so it is Lipschitz on the compact convex set closedBall(0, R) (bounded derivative plus the mean value inequality), and hence on A_R. Also J_G = 0 on A_R.
  - The general area formula (Simon Ch. 2, 3.4, for Lipschitz maps from measurable subsets of ℝ^n into ℝ^P with P ≥ n) gives ∫_{ℝ^P} H^0(G^{-1}(y) ∩ A_R) dH^n(y) = ∫_{A_R} J_G dL^n = 0. (The book text of 3.4 prints dH^m(y), a misprint for dH^n(y).)
  - The multiplicity H^0(G^{-1}(y) ∩ A_R) is ≥ 1 on the compact (hence Borel) set G(A_R). So H^n(G(A_R)) = 0.
  - Finally G(C) = ⋃_R G(A_R), so H^n(G(C)) = 0.
- In SimonGMT this is Chapter02.area_image_criticalSet_eq_zero. It holds for every map f : E → F between finite-dimensional real inner product spaces, is stated for μHE[finrank ℝ E], and here finrank ℝ ℝ^n = n. SimonGMT proves it by applying the injective area formula to the lifted maps x ↦ (G(x), εx) and letting ε ↓ 0.
2. (Candidate balls.) ℝ^n is separable and non-empty, so there is a sequence (e_q)_{q∈ℕ} dense in ℝ^n.
- For q, p ∈ ℕ put β_{q,p} := B_{1/(p+1)}(e_q).
- Call β_{q,p} good if there is μ > 0 with μ|a − b| ≤ |G(a) − G(b)| for all a, b ∈ β_{q,p}.
3. (Enumeration.) Fix a bijection ℕ → ℕ × ℕ, k ↦ (q_k, p_k), and write pair(q, p) for its inverse; for instance Mathlib's Nat.unpair with inverse Nat.pair. Put c_k := e_{q_k}.
- If β_{q_k,p_k} is good, put r_k := 1/(p_k + 1), and let m_k > 0 be a witness of goodness (chosen by the axiom of choice).
- Otherwise put r_k := 0 and m_k := 1.
4. (Positivity and (i).) In both cases m_k > 0.
- If β_{q_k,p_k} is good, then B_{r_k}(c_k) = β_{q_k,p_k}. By the choice of the witness, m_k|a − b| ≤ |G(a) − G(b)| for all a, b in it.
- Otherwise B_{r_k}(c_k) = B_0(c_k) = ∅, and (i) holds vacuously.
5. (Every regular point lies in one of the balls.) Let x ∉ C, so DG(x) is injective.
- By the sibling lemma local_lower_lipschitz, applied to G and x, there are δ > 0 and μ > 0 with μ|a − b| ≤ |G(a) − G(b)| for all a, b ∈ B_δ(x).
- By the Archimedean property choose p ∈ ℕ with 1/(p + 1) < δ/2. By density choose q ∈ ℕ with |x − e_q| < 1/(p + 1). Then x ∈ β_{q,p}.
- For a ∈ β_{q,p}, |a − x| ≤ |a − e_q| + |e_q − x| < 2/(p + 1) < δ. So β_{q,p} ⊆ B_δ(x), and μ witnesses that β_{q,p} is good.
- For k := pair(q, p) we have (q_k, p_k) = (q, p), so c_k = e_q and r_k = 1/(p + 1). Hence x ∈ B_{r_k}(c_k).
6. ((ii), covering.) Let y ∈ G(ℝ^n) ∖ ⋃_k G(B_{r_k}(c_k)), say y = G(x).
- If x ∉ C, step 5 gives k with x ∈ B_{r_k}(c_k). Then y ∈ G(B_{r_k}(c_k)), a contradiction. Hence x ∈ C and y ∈ G(C).
- Therefore G(ℝ^n) ∖ ⋃_k G(B_{r_k}(c_k)) ⊆ G(C).
- By monotonicity of the measure and step 1, H^n(G(ℝ^n) ∖ ⋃_k G(B_{r_k}(c_k))) ≤ H^n(G(C)) = 0. ∎

Implementation note (not part of the mathematics).
- Step 1 needs `import Poincare.SimonGMT.Chapter02.AreaCritical`. The module is prebuilt and compiles together with the frozen contract.
  - Use Poincare.SimonGMT.Chapter02.area_image_criticalSet_eq_zero G, rewritten with finrank_euclideanSpace_fin.
  - Use ContDiff.differentiable (by norm_num) for the differentiability conjunct.
- Other lemmas: TopologicalSpace.exists_dense_seq, DenseRange.exists_dist_lt, exists_nat_one_div_lt, half_pos, dist_triangle, Nat.pair, Nat.unpair, Nat.unpair_pair, ball_zero, Set.notMem_empty and measure_mono_null.
- Use `classical` for the if/dite on goodness, and Exists.choose / Exists.choose_spec for the witness.
- The sibling enters as Submission.codim1_rdo_c1cov_local_lower_lipschitz P n G x hG hinj.

## Key steps

1. Let C = {x : DG(x) not injective}. By the area formula (SimonGMT area_image_criticalSet_eq_zero), H^n(G(C)) = 0.
2. Fix a dense sequence (e_q) and candidate balls β_{q,p} = B_{1/(p+1)}(e_q). A ball is good if it admits a lower Lipschitz constant μ > 0.
3. Enumerate (q,p) by a bijection ℕ → ℕ × ℕ (Nat.unpair, inverse Nat.pair). Good balls get r_k = 1/(p_k+1) and a witness m_k > 0. The others get r_k = 0 and m_k = 1, so the ball is empty and the bound is vacuous.
4. For x ∉ C, local_lower_lipschitz gives B_δ(x) with constant μ. Choose p with 2/(p+1) < δ and q with |x − e_q| < 1/(p+1). Then β_{q,p} contains x, is good, and lies in B_δ(x), so x ∈ B_{r_k}(c_k) for k = pair(q,p).
5. Hence G(ℝ^n) ∖ ⋃_k G(B_{r_k}(c_k)) ⊆ G(C), which is H^n-null.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; diff -q <snapshot>/project/GMT/Ch07/Submission.lean GMT/Ch07/Submission.lean (identical)`
- `rg -n "c1cov|lower_lipschitz|regular_ball_cover|image_ball_borel" project mathlib/Mathlib (no match)`
- `rg -n "theorem approximates_deriv_on_nhds|theorem LinearMap.injective_iff_antilipschitz|theorem ContDiffOn.exists_lipschitzOnWith|theorem contDiff_piLp |theorem dist_apply_le|theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|theorem exists_dense_seq|theorem exists_inv_nat_lt|theorem bound_of_antilipschitz|theorem measure_iUnion_fintype_le" mathlib/Mathlib`
- `rg -n "AntilipschitzWith|antilipschitz" mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/*.lean mathlib/Mathlib/Analysis/Calculus/FDeriv/*.lean`
- `rg -n isSigmaCompact mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean | grep -i 'open\|ball' (no match)`
- `grep -rn 'theorem le_of_forall_lt' mathlib/Mathlib/Order (to_dual le_of_forall_gt)`
- `grep -n area_image_criticalSet_eq_zero simongmt Chapter02/AreaCritical.lean; grep -n euclideanHausdorffMeasure_image_le_of_lipschitzOn Chapter02/Lipschitz.lean; sed -n 1,60p Chapter03/SubmanifoldCover.lean; sed -n 1,150p Chapter03/Rectifiable.lean; ls .lake/build/lib/lean/Poincare/SimonGMT/Chapter02 (AreaCritical.olean present)`
- `python3 scans of dag.json: nodes under rectifiable_density_one-a1 (lean_name/status/lean_statement); lean_statements containing 'Injective (fderiv' with ball, "'' ball", 'AntilipschitzWith', 'volume {x'; subtree of dpf_rectifiable_bilipschitz_pieces (accepted a2ba78fc)`
- `grep -c codim1_rdo_c1cov_{local_lower_lipschitz,regular_ball_cover,image_ball_borel_finite,lipschitz_range_c1_cover} dag.json (0 each); git log --all --oneline -S'c1cov' (none)`
- `sed -n 1801,1999p and 6500,6640p /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py (_solve_children, _dependency_problem, _existing_lean_name_problem)`
- `lake env lean -DautoImplicit=false /tmp/c1cov-split-check/final/TypesFinal.lean`
- `lake env lean -DautoImplicit=false /tmp/c1cov-split-check/final/CombinedFinal.lean (#print axioms of four children and parent)`
- `lake env lean -DautoImplicit=false /tmp/c1cov-split-check/importcheck/SubmissionWithAreaCritical.lean`
- `sed -n 1,90p book/chapter-03.txt; sed -n 160,180p, 268,300p, 740,800p book/chapter-02.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-604cc328a3/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/c1cov-split-check/final/statements.json`
- `/tmp/c1cov-split-check/final/TypesFinal.lean`
- `/tmp/c1cov-split-check/final/CombinedFinal.lean`
- `/tmp/c1cov-split-check/importcheck/SubmissionWithAreaCritical.lean`
- `/tmp/c1cov-split-check/out/subproblems.json`
- `/tmp/c1cov-review/NoExtra.lean`

Pins and contract.
- The manifest pins project b4d606db and Mathlib 25730c7c, matching the workspace.
- The snapshot's project/GMT/Ch07/Submission.lean is identical to the workspace contract.

Mathlib (snapshot).
- It provides every analytic tool the children use: LinearMap.injective_iff_antilipschitz, ZeroHomClass.bound_of_antilipschitz, HasStrictFDerivAt.approximates_deriv_on_nhds, ContDiffOn.exists_lipschitzOnWith, contDiff_piLp, PiLp.dist_apply_le, TopologicalSpace.exists_dense_seq, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, measure_iUnion_fintype_le, ENNReal.exists_inv_nat_lt and le_of_forall_gt.
- It has no lower-Lipschitz lemma for an injective, non-surjective derivative: ApproximatesLinearOn.antilipschitzWith requires an equivalence E ≃L F.
- It has no σ-compactness lemma for open balls (no match in SigmaCompact.lean).
- So local_lower_lipschitz and the closed-ball exhaustion in image_ball_borel_finite are genuine obligations.

SimonGMT (pinned package).
- area_image_criticalSet_eq_zero (Chapter02/AreaCritical; prebuilt olean, needs one extra import) holds for every f : E → F.
- euclideanHausdorffMeasure_image_le_of_lipschitzOn (Chapter02/Lipschitz) is already in the contract's import closure.
- The Chapter03/SubmanifoldCover docstring says the 'only if' direction of Lemma 1.2 is not proved.

DAG.
- No accepted node supplies these lemmas. dpf_rectifiable_bilipschitz_pieces is a single declaration with Lipschitz (not C¹) pieces and needs MeasurableSet M.
- The parent's dependency codim1_rdo_c1_approximation is an active node under another parent. It cannot be a child of this node, so it enters child lipschitz_range_c1_cover as a verbatim hypothesis, which the parent discharges.
- The four new names have 0 matches in dag.json, in git history and in the snapshot.

Lean.
- TypesFinal.lean compiles: all child types elaborate with only the contract import, and comparator-style restatements check.
- SubmissionWithAreaCritical.lean compiles: the contract builds with the AreaCritical import added.
- CombinedFinal.lean compiles. All four children use only propext, Classical.choice and Quot.sound. The parent's exact frozen type follows from the child types, and its only extra axiom is sorryAx from the stub for codim1_rdo_c1_approximation.
