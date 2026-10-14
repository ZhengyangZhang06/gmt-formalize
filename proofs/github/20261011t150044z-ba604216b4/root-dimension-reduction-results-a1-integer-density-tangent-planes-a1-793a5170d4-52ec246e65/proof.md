# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1.spine_coarea-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Registration and depth note (context, not part of the numbered proof). Fresh name idtp_fons_cs_sos_spine_coarea. Its frozen type is byte-identical to that of dimred_cs_sos_spine_coarea (DAG node root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.spine_coarea-a1, status decomposing), which is owned by the other parent root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1 (the node whose frozen type equals the selected node's) and is not comparator-accepted, so the runtime forbids reusing that name here. The numbered proof below is that node's independently audited parent-supplied proof, changed only as stated here. This node sits at depth 6, the configured maximum, so it is a machine leaf: its Lean proof adds only Submission.idtp_fons_cs_sos_spine_coarea, proves every auxiliary claim below inline (have/obtain/let/show), and adds no helper declaration and no import. The declarations of its listed dependencies are available because the controller merges their accepted candidates into this leaf's worktree before its implementation base is recorded. Changes: only the Imports paragraph below. The AreaLipschitz import now arrives with the accepted dependency dpf_piece. The sibling lipschitz_tangent of (T3) is Submission.idtp_fons_cs_sos_lipschitz_approx_tangent, with the same frozen type as before.

Notation and tools.
- q := I − p = Lᗮ.starProjection, so x = p(x) + q(x) with p(x) ∈ L and q(x) ∈ L^⊥.
- On a k-dimensional subspace, H^k is k-dimensional Lebesgue measure. This follows from isometry invariance of μHE and EuclideanSpace.euclideanHausdorffMeasure_eq_volume.
- Jacobians. For a linear D : ℝ^k → ℝ^P, J(D) := det(D*D)^{1/2}. For a Lipschitz F : ℝ^k → ℝ^P, JF(u) := J(DF(u)) where F is differentiable (Rademacher: a.e.).
- G_F := {u : F differentiable at u, DF(u) injective}.
Facts used:
(T1) Area formula and Lipschitz images.
 - (T1a) Area formula: for F : ℝ^k → ℝ^P Lipschitz and injective on a Borel set B, and Borel g ≥ 0, ∫_{F(B)} g dH^k = ∫_B g(F(u)) JF(u) du (SimonGMT weighted_area_formula_lipschitz_injOn).
 - (T1b) Sard-type statement: H^k(F(ℝ^k ∖ G_F)) = 0 (SimonGMT area_image_compl_regularSet_eq_zero).
 - (T1c) Lipschitz image bound: H^k(F(Z)) ≤ Lip(F)^k L^k(Z) for every Z (SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn).
 Imports. (T1a) and (T1b) are in Poincare.SimonGMT.Chapter02.AreaLipschitz, outside the contract import closure; they are used in steps 1 and 5. (T1c) is in scope via Chapter02.Lipschitz. This leaf adds no import. Its dependency dpf_piece is the accepted Submission.dpf_approxTangent_ae_bilipschitz_piece. Its accepted candidate commit a21680472b6919972de04d02dc3e1395a15d4171 already has `import Poincare.SimonGMT.Chapter02.AreaLipschitz` in GMT/Ch07/Submission.lean, and the controller merges accepted dependency candidates into this node's worktree before the implementation base is recorded. The import also arrives through lipschitz_tangent, which depends on dpf_piece. dpf_piece is used here only for this import.
 All other facts cited below are in scope after `import GMT.Ch07.Submission`.
(T2) Bi-Lipschitz pieces (Mathlib exists_partition_approximatesLinearOn_of_hasFDerivWithinAt). Let G ⊆ ℝ^k be Borel with F differentiable at every point of G, and let r be a function on linear maps with r(A) > 0 for every A; we use r(A) := c_A/16 if A is injective and r(A) := 1 otherwise, where c_A := min_{|w|=1}|Aw|. Then G ⊆ ⋃_i t_i for pairwise disjoint Borel sets t_i, with linear maps A_i such that:
 - |F(v) − F(w) − A_i(v − w)| ≤ r(A_i)|v − w| for v, w ∈ G ∩ t_i;
 - if G ∩ t_i ≠ ∅, then A_i = DF(y_i) for some y_i ∈ G (not necessarily in t_i).
(T3) Tangent planes along Lipschitz maps: the sibling child lipschitz_tangent. Let k ≥ 1, F : ℝ^k → ℝ^P Lipschitz, and Y ⊆ ℝ^P Borel and locally H^k-finite. Then for L^k-a.e. u with F(u) ∈ Y and u ∈ G_F, Y has approximate tangent space DF(u)(ℝ^k) at F(u).
(T5) Fubini. A linear isometry ℝ^d × ℝ^m ≅ L × K (orthonormal coordinates) carries product Lebesgue measure to H^d⌞L ⊗ H^m⌞K. Use Mathlib Submodule.measurePreserving_measurableEquivProd and Tonelli (lintegral_prod).

(T4) Eilenberg inequality for p. If Z ⊆ ℝ^P and H^n(Z) = 0, then H^m(Z ∩ p⁻¹(t)) = 0 for H^d-a.e. t ∈ L.
Proof: H^n(Z) = 0 means μH[n](Z) = 0. So for each j there is a countable cover (C_i^j)_i of Z with diam C_i^j < 1/j and Σ_i (diam C_i^j)^n < 4^{−j}. Put
 φ_j(t) := Σ_i 1_{p(cl C_i^j)}(t)(diam C_i^j)^m.
 This is Borel: p(cl C) is compact for bounded C. Since p is 1-Lipschitz, p(cl C_i^j) lies in a ball of L of radius diam C_i^j, so H^d(p(cl C_i^j)) ≤ ω_d (diam C_i^j)^d. Therefore
 ∫_L φ_j dH^d ≤ ω_d Σ_i (diam C_i^j)^n < ω_d 4^{−j}.
 By Markov's inequality and Borel–Cantelli, φ_j(t) → 0 for H^d-a.e. t ∈ L. For such t, the sets C_i^j with t ∈ p(C_i^j) cover Z ∩ p⁻¹(t). Hence the 1/j-premeasure satisfies μH[m]_{1/j}(Z ∩ p⁻¹(t)) ≤ φ_j(t) → 0. These premeasures increase to μH[m](Z ∩ p⁻¹(t)) as j → ∞, so that value is 0. ∎(T4)

Main proof.
1. (Parametrization.) By countable rectifiability, M ⊆ M₀ ∪ ⋃_j F_j(ℝ^n) with H^n(M₀) = 0 and F_j : ℝ^n → ℝ^P Lipschitz. By (T1b), H^n(F_j(ℝ^n ∖ G_{F_j})) = 0.
2. (Good parameters.)
 - Bad points of M. Let Bad ⊆ M be the H^n-null set of x ∈ M at which no approximate tangent space Q ⊇ L exists, and let Bad' ⊇ Bad be Borel and H^n-null.
 - The sets E_j. Put E_j := G_{F_j} ∩ F_j⁻¹(M ∖ Bad'), a Borel set. By (T3) applied to (F_j, Y := M), there is a Borel L^n-null set N_j such that for u ∈ E_j ∖ N_j, M has approximate tangent space DF_j(u)(ℝ^n) at F_j(u). This space contains L, by uniqueness of approximate tangent spaces (SimonGMT HasApproximateTangentSpaceAt.unique) and F_j(u) ∉ Bad.
 - The sets U'_j. Put U'_j := E_j ∖ N_j (Borel). By (T1c), H^n(F_j(N_j)) = 0. Hence M ∖ ⋃_j F_j(U'_j) ⊆ M₀ ∪ Bad' ∪ ⋃_j [F_j(ℝ^n ∖ G_{F_j}) ∪ F_j(N_j)] is H^n-null.
 Apply (T2) to F_j on G := U'_j. This gives countably many Borel pieces T := U'_j ∩ t_i, with F := F_j and A = A_T = DF(u_T) for some u_T ∈ U'_j, such that:
 (a) |F(v) − F(w) − A(v − w)| ≤ (c_A/16)|v − w| on T, hence |F(v) − F(w)| ≥ (15c_A/16)|v − w| on T;
 (b) every u ∈ T is good: F(u) ∈ M, DF(u) is injective, and T_{F(u)}M = DF(u)(ℝ^n) ⊇ L;
 (c) A is injective and L ⊆ A(ℝ^n), because u_T ∈ U'_j is good.
 The union of the images F(T) over all pieces covers M up to an H^n-null set.
3. (Adapted coordinates on a piece.)
 - Surjectivity of p∘A. Let ℓ ∈ L. By (c) there is w with Aw = ℓ and |w| ≤ |ℓ|/c_A, and then p(Aw) = ℓ. So p∘A : ℝ^n → L is onto.
 - Splitting. K := ker(p∘A) has dimension m. On K' := K^⊥ we have |pAa| ≥ c_A|a|, since the minimal-norm preimage lies in K'.
 - The map Φ. Define Φ : ℝ^n → L × K by Φ(u) := (pF(u), π_K u).
 - Φ is bi-Lipschitz on T. For v, w ∈ T write v − w = a + b with a ∈ K' and b ∈ K. Then pF(v) − pF(w) = pAa + p(e) with |e| ≤ (c_A/16)(|a| + |b|).
  - If |b| ≥ |a|: |Φ(v) − Φ(w)| ≥ |b| ≥ |v − w|/√2.
  - If |b| < |a|: |pF(v) − pF(w)| ≥ c_A|a| − (c_A/8)|a| ≥ (7c_A/8)|v − w|/√2.
  So |Φ(v) − Φ(w)| ≥ κ|v − w| on T, with κ := min(1, 7c_A/8)/√2 > 0.
 - The parametrization H. Ω := Φ(T) is Borel (Lusin–Souslin). H := F∘(Φ|_T)⁻¹ : Ω → ℝ^P is Lipschitz and injective, with Lipschitz inverse Φ∘(F|_T)⁻¹ on F(T). Extend H to a Lipschitz map L × K → ℝ^P coordinatewise (McShane: LipschitzOnWith.extend_real applied to each coordinate of an orthonormal basis of ℝ^P).
 - p(H(t, b)) = t for (t, b) ∈ Ω.
 - Identify L × K with ℝ^n through orthonormal coordinates as in (T5).
4. (Jacobian identity.) Fix (t, b) ∈ Ω such that:
 - (t, b) is a density point of Ω;
 - H is differentiable at (t, b);
 - with x := H(t, b), DH(t, b) is injective and M has approximate tangent space DH(t, b)(ℝ^n) at x.
 These hold at L^n-a.e. (t, b) ∈ Ω: Rademacher; the lower Lipschitz bound |H(z) − H(z')| ≥ κ'|z − z'| on Ω (κ' > 0, step 3) passes to DH at Lebesgue density points z of Ω where H is differentiable. Given |w| = 1 and ε ∈ (0, 1), for small ρ the ball B_{ερ}(z + ρw) meets Ω, since otherwise a fixed fraction of B_{2ρ}(z) misses Ω. A point z_ρ there gives κ'(1 − ε)ρ ≤ |H(z_ρ) − H(z)| ≤ ρ|DH(z)w| + ‖DH(z)‖ερ + o(ρ), so |DH(z)w| ≥ κ' after letting ρ ↓ 0 and then ε ↓ 0. Finally, (T3) applies to (H, M).
 By uniqueness and step 2(b), R := DH(t, b)(ℝ^n) = T_xM ⊇ L.
 - Differentiating p∘H(t', b') = t' along Ω at a density point gives p∘∂_tH = id_L and p∘∂_bH = 0, where DH = [∂_tH | ∂_bH] with ∂_tH : L → ℝ^P and ∂_bH : K → ℝ^P.
 - Hence ∂_bH(K) ⊆ R ∩ L^⊥. Since L ⊆ R, we have R = L ⊕ (R ∩ L^⊥) and dim(R ∩ L^⊥) = m. ∂_bH is injective, so ∂_bH(K) = R ∩ L^⊥.
 - For ℓ ∈ L, ∂_tH(ℓ) − ℓ = q∂_tH(ℓ) ∈ R ∩ L^⊥. So ∂_tH(ℓ) = ℓ + ∂_bH(Bℓ) for a linear B : L → K.
 - Thus DH(t, b) = D₀∘U, with D₀(ℓ, κ) := ℓ + ∂_bH(κ) and U(ℓ, κ) := (ℓ, κ + Bℓ). U is unipotent, so det U = 1.
 - D₀ maps L isometrically into L and K into L^⊥ ⊥ L. So D₀*D₀ = diag(I_L, (∂_bH)*∂_bH).
 - Hence J(DH(t, b)) = J(D₀)|det U| = J(∂_bH(t, b)) =: J_bH(t, b), and ∂_bH(t, b)(K) = T_xM ∩ L^⊥.
5. (Coarea on one piece.) Let g ≥ 0 be Borel. By (T1a) for H on Ω and step 4,
 ∫_{F(T)} g dH^n = ∫_Ω g(H) JH = ∫_Ω g(H) J_bH.
 By Tonelli on L × K this equals ∫_L (∫_{Ω_t} g(H(t, b)) J_bH(t, b) db) dt, where Ω_t := {b : (t, b) ∈ Ω}; the inner integral is measurable in t.
 For each t, H_t := H(t, ·) : K → ℝ^P is Lipschitz and injective on Ω_t, and H_t(Ω_t) = F(T) ∩ p⁻¹(t). Indeed every x ∈ F(T) with p(x) = t is H(t, π_K(F|_T)⁻¹x).
 By Tonelli applied to the null set of bad (t, b), for H^d-a.e. t the following holds for L^m-a.e. b ∈ Ω_t: H_t is differentiable at b with DH_t(b) = ∂_bH(t, b).
 Hence, for a.e. t, (T1a) for H_t gives ∫_{F(T) ∩ p⁻¹(t)} g dH^m = ∫_{Ω_t} g(H(t, b)) J_bH(t, b) db.
 Therefore ∫_{F(T)} g dH^n = ∫_L ∫_{F(T)∩p⁻¹(t)} g dH^m dt, with an a.e.-measurable inner function.
6. (Summation; proof of (ii).)
 - Disjoint pieces. Enumerate the pieces as (T_l, F_l, H_l, Ω_l)_{l∈ℕ}. Put P'_l := F_l(T_l) ∖ ⋃_{l'<l} F_{l'}(T_{l'}). These sets are Borel and pairwise disjoint, their union is N_M := ⋃_l F_l(T_l) ⊆ M, and Z := M ∖ N_M is Borel with H^n(Z) = 0 (step 2).
 - Applying step 5 to g·1_{P'_l} and summing by monotone convergence gives ∫_{N_M} g dH^n = ∫_L ∫_{N_M ∩ p⁻¹(t)} g dH^m dt.
 - By (T4), H^m(Z ∩ p⁻¹(t)) = 0 for a.e. t, so ∫_{M_t} g dH^m = ∫_{N_M ∩ p⁻¹(t)} g dH^m for a.e. t.
 - Also ∫_M g dH^n = ∫_{N_M} g dH^n, which proves (ii). The a.e.-measurability holds because a countable sum of a.e.-measurable functions is a.e.-measurable.
7. (Rectifiable slices.) For every t, N_M ∩ p⁻¹(t) = ⋃_l (P'_l ∩ p⁻¹(t)) ⊆ ⋃_l H_l(t, ·)(K_l), and each H_l(t, ·) is a Lipschitz map on K_l ≅ ℝ^m. With H^m(Z ∩ p⁻¹(t)) = 0 for a.e. t (step 6), M_t is countably m-rectifiable for a.e. t, taking Z ∩ p⁻¹(t) as the exceptional set M₀ of the definition.
8. (Tangent planes of slices; proof of (i).)
 - Local finiteness. By (ii) with g = 1_{B̄_j}, ∫_L H^m(M_t ∩ B̄_j) dt = H^n(M ∩ B̄_j) < ∞. So for a.e. t, M_t is locally H^m-finite (countably many j).
 - Fix l. For a.e. t, apply (T3) to the Lipschitz map H_l(t, ·) and Y := M_t (Borel, locally finite). For L^m-a.e. b ∈ (Ω_l)_t such that (t, b) is good in step 4, M_t has approximate tangent space ∂_bH_l(t, b)(K_l) = T_xM ∩ L^⊥ at x = H_l(t, b). Here DH_l(t, ·)(b) = ∂_bH_l(t, b) is injective.
 - The bad (t, b) form a null set, so for a.e. t only an L^m-null set of b is bad. By (T1c), H_l(t, ·) maps these null sets to H^m-null sets.
 - Hence, for a.e. t and H^m-a.e. x ∈ P'_l ∩ p⁻¹(t), M_t has approximate tangent space T_xM ∩ L^⊥ at x. Take the union over l and add the null part Z ∩ p⁻¹(t).
 - If Q is any subspace with HasApproximateTangentSpaceAt n M x Q, then Q = T_xM by uniqueness. So HasApproximateTangentSpaceAt m M_t x (Q ∩ L^⊥), and finrank(Q ∩ L^⊥) = n − d = m because L ⊆ Q. This proves (i). ∎

## Key steps

1. Cover M, up to an H^n-null set, by Lipschitz pieces F(T) on which F is bi-Lipschitz and close to an injective linear A with L ⊆ A(ℝ^n), using the sibling lipschitz_tangent: T_{F(u)}M = DF(u)(ℝ^n).
2. On each piece Φ = (p∘F, π_{ker pA}) is bi-Lipschitz, so the piece is H(Ω) with H Lipschitz, injective, and p(H(t, b)) = t.
3. Since L ⊆ range DH, Gram-determinant column operations give JH = J_bH and ∂_bH(K) = T_xM ∩ L^⊥.
4. The area formula for H and for each H(t, ·) (SimonGMT AreaLipschitz, imported through the accepted dependency dpf_piece), with Tonelli, gives the coarea identity on each piece. Summing over disjoint pieces and the Eilenberg inequality for the null remainder gives (ii).
5. Slices are covered by Lipschitz images of ℝ^m (rectifiable), and lipschitz_tangent for H(t, ·) gives Tan(M_t, x) = T_xM ∩ L^⊥ a.e., which is (i).

## Reference use

### local-project

Queries:
- `python3 -I -c json.load(<snap>/manifest.json); git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `cmp GMT/Ch07/Contract.lean <snap>/project/GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n '^def (IsMinimizingIn|IsConeCurrent|BoundaryVanishes|SameBoundary|blowUp|currentEval|approxTangentPlane)|^structure IMRep|^def IMRep\.(measure|Represents|action)' <snap>/project/GMT/Ch07/Contract.lean`
- `rg -n -i -l coarea <snap>/mathlib/Mathlib (no match)`
- `rg -n -i -l 'cartesian product of currents|slice of a current' <snap>/mathlib/Mathlib (no match)`
- `rg -n 'idtp_fons_cs_sos|dimred_cs_sos|dpf_approxTangent_ae_bilipschitz_piece|dimred_im_mass_measure' <snap>/project (no match)`
- `rg -n 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt' <snap>/mathlib/Mathlib`
- `rg -n 'theorem measurableSet_of_differentiableAt|theorem measurable_fderiv' <snap>/mathlib/Mathlib`
- `rg -n "theorem ae_all_iff|theorem ae_restrict_iff'" <snap>/mathlib/Mathlib`
- `rg -n 'theorem isOpen_iUnion_countable' <snap>/mathlib/Mathlib/Topology/Bases.lean; rg -n 'theorem ContinuousLinearMap.isOpen_injective' <snap>/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean; rg -n 'theorem MeasureTheory.Measure.euclideanHausdorffMeasure_zero ' <snap>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -n 'theorem weighted_area_formula_lipschitz_injOn|theorem area_image_compl_regularSet_eq_zero|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn|def areaRegularSet|theorem measurableSet_areaRegularSet' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/{AreaLipschitz,Lipschitz}.lean`
- `python3 scans of dag.json: status, candidate_commit, lean_statement, parent of dimred_cs_split_off_spine, dimred_cs_sos_*, the 5 reuses and all accepted nodes; accepted candidates whose Submission.lean imports Poincare.SimonGMT.Chapter02.AreaLipschitz; absence of the 7 fresh names`
- `git show <candidate_commit>:GMT/Ch07/Submission.lean for the 5 reuses (declaration with identical type present; a21680472b has import Poincare.SimonGMT.Chapter02.AreaLipschitz)`
- `cat cluster-state/verification/results/hoa43/20261013T160813Z-ch07-root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_densit-ej3048p6/{result.json,comparator-config.json}`
- `grep -n '_existing_lean_name_problem|_dependency_problem|_overlay_accepted_children|_leaf_author_task|max_depth' /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `lake env lean /tmp/idtp_sos_decomp/check/{Types,Names,NamesArea,Assembly,Assembly2,Assembly3}.lean`
- `python3 /tmp/idtp_sos_decomp/scripts/gates.py /tmp/idtp_sos_decomp/envelope_test3.json (ScopedDecomposition.model_validate; replay of Runtime._dependency_problem, _topological, _existing_lean_name_problem on dag.json)`
- `sed -n 395,420p book/chapter-07.txt (Simon Lemma 7.3.5)`
- `WebSearch: Simon Introduction to GMT Lemma 3.5 minimizing cone translation invariant S = [[R^m]] × S_0`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ac0f702949/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-680a7024c9/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/models.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/idtp_sos_decomp/check/Assembly3.lean`
- `/tmp/idtp_sos_decomp/check/NamesArea.lean`
- `/tmp/idtp_sos_review/LipCheck.lean`
- `/tmp/idtp_sos_review/CarrierCheck.lean`
- `/tmp/idtp_sos_review/UsageCheck.lean`

Pins match: the snapshot manifest records project b4d606d (= workspace HEAD) and Mathlib 25730c7c (= workspace Mathlib); SimonGMT is 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, which hold no Submission declarations; none of the 7 fresh names, nor the reused names, occur in the snapshot project. No coarea formula, slicing or Cartesian product of currents exists in the snapshot Mathlib (no match). Mathlib does have exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, measurableSet_of_differentiableAt, measurable_fderiv, ContinuousLinearMap.isOpen_injective, TopologicalSpace.isOpen_iUnion_countable and euclideanHausdorffMeasure_zero, all used by the child proofs. SimonGMT's area formula (weighted_area_formula_lipschitz_injOn, area_image_compl_regularSet_eq_zero, measurableSet_areaRegularSet) lies in Chapter02/AreaLipschitz.lean, outside the contract imports. In dag.json, the accepted dpf_approxTangent_ae_bilipschitz_piece (candidate a21680472b, comparator passed with propext, Quot.sound, Classical.choice) carries that import and proves the bi-Lipschitz-piece tangent lemma. The 5 reused declarations are accepted with byte-identical types present in their candidate commits. The six dimred_cs_sos_* children of the identical-type node dimred_cs_split_off_spine are unaccepted and owned by another parent, hence the fresh names. All 12 child types and the parent type elaborate. The parent assembly and the product_current usage checks compile; #print axioms shows only propext, Classical.choice and Quot.sound beyond the stubs' sorryAx. The runtime gate replay reports no problem.
