# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1.product_decomposition-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Registration and depth note (context, not part of the numbered proof). Fresh name idtp_fons_cs_sos_product_decomposition. Its frozen type is byte-identical to that of dimred_cs_sos_product_decomposition (DAG node root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.product_decomposition-a1, status decomposing), which is owned by the other parent root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1 (the node whose frozen type equals the selected node's) and is not comparator-accepted, so the runtime forbids reusing that name here. The numbered proof below is that node's independently audited parent-supplied proof, changed only as stated here. This node sits at depth 6, the configured maximum, so it is a machine leaf: its Lean proof adds only Submission.idtp_fons_cs_sos_product_decomposition, proves every auxiliary claim below inline (have/obtain/let/show), and adds no helper declaration and no import. The declarations of its listed dependencies are available because the controller merges their accepted candidates into this leaf's worktree before its implementation base is recorded. Changes: the measure-uniqueness lemma imrep_measure_eq_of_represents_same_current is replaced by part (c) of the accepted dimred_im_mass_measure (sibling im_mass_measure), which states the same fact. The child spine_coarea is Submission.idtp_fons_cs_sos_spine_coarea, with the same frozen type as before.

Notation. p := L.starProjection and q := I − p = Lᗮ.starProjection. H^k := μHE[k]; on k-dimensional subspaces it is Lebesgue measure. M_t := M ∩ p⁻¹(t) for t ∈ L. "IMRep" means an IMRep univ of the stated dimension. Let ♭ be a map as in the statement.
Accepted declarations used (DAG reuse siblings):
- dtc_imrep_current (sibling imrep_current): every IMRep defines a current that it represents.
- imrep_weighted_orient_indicator_ae_eq (sibling orient_data_unique): two representations of one current in an open set have H^n-a.e. equal data 1_M θ ξ on the union of their carriers.
- dimred_im_mass_measure (sibling im_mass_measure), part (c): two representations of one current have the same measure. Precisely, if R represents T in an open U, then every representation R' of T in U has R'.measure = R.measure.
Child used: spine_coarea.
1. (♭ is the interior product.) The defining identity determines ♭α. Hence ♭(α + β) = ♭α + ♭β and ♭(cα) = c♭α; evaluate at each v. Also ‖♭α‖ ≤ ‖α‖, since f is orthonormal. So ♭ is continuous linear. For every test n-form ω and t ∈ ℝ^P, the form y ↦ ♭(ω(t + y)) is C^∞ with tsupport ⊆ tsupport ω − t, compact; it is a test m-form, so currentEval S₀ of it equals S₀ applied to it.
2. (Lift.) There is a continuous linear lift : Λ^m → Λ^n with (lift β)(f_1, …, f_d, w_1, …, w_m) = β(w_1, …, w_m) for all w_j ∈ L^⊥. Equivalently, (♭(lift β))(w) = β(w) for w ∈ (L^⊥)^m.
 Construction: (lift β)(v_1, …, v_n) := (1/m!) Σ_{σ∈S_n} sgn(σ) ∏_{a=1}^d ⟨f_a, v_{σ(a)}⟩ · β(q v_{σ(d+1)}, …, q v_{σ(n)}), the alternatization (Mathlib MultilinearMap.alternatization) of a multilinear map.
 Evaluation at (f, w) with w_j ∈ L^⊥: a term is nonzero only if v_{σ(a)} = f_a for every a ≤ d, because ⟨f_a, w_j⟩ = 0 and ⟨f_a, f_b⟩ = δ_ab. So σ fixes 1, …, d. The remaining sum is Σ_{π∈S_m} sgn(π) β(w_π) = m! β(w).
3. (Orientation decomposition.)
 - Borel version of ξ. Let ξ̃ be Borel with ξ̃ = ξ H^n⌞M-a.e. (AEStronglyMeasurable.mk). R̃ := (M, θ, ξ̃) is an IMRep representing S with R̃.measure = μ; the integrands of the action agree a.e.
 - The good set G. Let G be the set of x ∈ M such that:
  - ξ̃(x) = ξ(x);
  - for some Q_x, HasApproximateTangentSpaceAt n M x Q_x holds and ξ(x) is a unit orientation of Q_x (R.orients);
  - L ⊆ Q_x.
  The last condition follows from the hypothesis: approxTangentPlane n M x = Q_x by uniqueness, and starProjection_eq_self_iff. Since μ = θH^n⌞M with θ ≥ 1 on M, μ-a.e. is the same as H^n⌞M-a.e. Hence H^n(M ∖ G) = 0, and G contains a Borel set G' ⊆ M with H^n(M ∖ G') = 0.
 - The m-vector field ζ. Define ζ(x)(β) := ξ̃(x)(lift β); ζ : ℝ^P → MultiVector P m is Borel.
 - Structure at x ∈ G. Q_x = L ⊕ (Q_x ∩ L^⊥) with dim(Q_x ∩ L^⊥) = m. Take an orthonormal basis g of Q_x ∩ L^⊥; then (f, g) is an orthonormal basis of Q_x. If ξ(x)(α) = ±α(τ) for an orthonormal basis τ of Q_x, then τ = O(f, g) with O orthogonal and α(τ) = det(O)α(f, g). So ξ(x)(α) = εα(f, g) for all α, with ε = ±1.
 - Consequences, for x ∈ G:
  (a) ζ(x)(β) = ε(lift β)(f, g) = εβ(g), so ζ(x) is a unit orientation of Q_x ∩ L^⊥ and ‖ζ(x)‖ ≤ 1;
  (b) ξ(x)(α) = εα(f, g) = ε(♭α)(g) = ζ(x)(♭α) for every α.
4. (Coarea.) The child spine_coarea applies to M: M is Borel, countably n-rectifiable, H^n(M ∩ K) ≤ μ(K) < ∞, and tangent planes contain L on G. Write ν_t := H^m⌞M_t. We obtain:
 (C1) for Borel g ≥ 0: ∫_M g dH^n = ∫_L ∫ g dν_t dt, with t ↦ ∫ g dν_t a.e.-measurable;
 (C2) if Z ⊆ M is contained in a Borel H^n-null set Z', then ν_t(Z) ≤ ν_t(Z') = 0 for a.e. t (C1 with g = 1_{Z'});
 (C3) for a.e. t: M_t is countably m-rectifiable, and for ν_t-a.e. x, HasApproximateTangentSpaceAt m M_t x (Q ∩ L^⊥) for every Q with HasApproximateTangentSpaceAt n M x Q.
5. (Slice representations.)
 - The set 𝒯. Let 𝒯 ⊆ L be the set of t such that:
  - (C3) holds at t;
  - ν_t(M ∖ G') = 0 (C2);
  - ∫_{M_t ∩ B̄_j} θ dH^m < ∞ for all j ∈ ℕ. By (C1), ∫_L ∫_{M_t∩B̄_j} θ dH^m dt = μ(B̄_j) < ∞.
  𝒯 has full H^d⌞L-measure.
 - R_t is an IMRep. For t ∈ 𝒯, R_t := (M_t, θ, ζ) is an IMRep of dimension m:
  - the carrier is Borel and countably m-rectifiable;
  - θ is measurable with θ ≥ 1 on M_t, and locally integrable (every compact set lies in some B̄_j);
  - ζ is Borel;
  - orients: for ν_t-a.e. x we have x ∈ G' ⊆ G, so ζ(x) is a unit orientation of Q_x ∩ L^⊥ (step 3a), and M_t has approximate tangent space Q_x ∩ L^⊥ at x (C3).
 - Action formula. Let ω be a test n-form. Write h(x) := θ(x)ζ(x)(♭ω(x)) for x ∈ M; |h| ≤ θ‖ω‖_∞1_{tsupport ω} on G. By step 3b and (C1) applied to h⁺ and h⁻ (finite integrals),
  S(ω) = ∫_M θξ(ω) dH^n = ∫_M h dH^n = ∫_L (∫_{M_t} θζ(♭ω) dH^m) dt = ∫_L R_t.action(♭ω) dt.
 - Measure formula. For Borel A, by (C1): μ(A) = ∫_M θ1_A dH^n = ∫_L R_t.measure(A) dt.
6. (Translation invariance of the data.) Let v ∈ L.
 - Define R^v := (M + v, θ(· − v), ξ̃(· − v)). It is an IMRep: translation preserves Borel sets, Lipschitz covers, local integrability and H^n. Moreover HasApproximateTangentSpaceAt n (M + v) (x + v) Q ⟺ HasApproximateTangentSpaceAt n M x Q, because η_{x+v,r}(M + v) = η_{x,r}(M).
 - R^v represents S. By translation invariance of H^n, R^v.action(ω) = ∫_M θξ̃(ω(· + v)) dH^n = S(ω(v + ·)). The map blowUp S (−v) 1 is the affine push-forward along y ↦ v + y, so S(ω(v + ·)) = currentEval (blowUp S (−v) 1) ω = S(ω) by hypothesis.
 - Applying the two accepted lemmas to R̃ and R^v (both represent S in the open set ℝ^P):
  (i) θ·H^n⌞M = θ(· − v)·H^n⌞(M + v). Both are withDensity measures of the σ-finite H^n⌞(M ∪ (M + v)), so 1_Mθ(z) = 1_{M+v}(z)θ(z − v) for H^n-a.e. z;
  (ii) 1_M(z)θ(z)ξ̃(z) = 1_{M+v}(z)θ(z − v)ξ̃(z − v) for H^n-a.e. z ∈ M ∪ (M + v).
 - Let Γ(z) := (1_M(z)θ(z), 1_M(z)θ(z)ξ̃(z)), a Borel map. Then Γ(z) = Γ(z − v) for H^n-a.e. z, on M ∪ (M + v) by (i)–(ii) and trivially off it.
7. (Selection of a base slice by Fubini.)
 - The sets B and B'. Let B := {(v, x) ∈ L × ℝ^P : x ∈ M, Γ(x + v) ≠ Γ(x)} and B' := {(v, x) : x ∈ M, Γ(x − v) ≠ Γ(x)}; both are Borel. For each v, B_v = {x ∈ M : Γ(x + v) ≠ Γ(x)} is the translate by −v of {z ∈ M + v : Γ(z) ≠ Γ(z − v)}, which is H^n-null by step 6; so H^n(B_v) = 0. Likewise B'_v ⊆ {z : Γ(z) ≠ Γ(z − v)} is H^n-null.
 - A measurable version of the slices.
  - Exhausting boxes. Let C_j := {x : |x_i| < j for all i}. Let 𝒫 be the countable π-system of open boxes with rational corners; it generates the Borel σ-algebra and contains every C_j.
  - Choice of N₀. By (C1), for each Z ∈ 𝒫 the map s ↦ ν_s(Z) is a.e.-measurable, and it is finite a.e. because ∫_L ν_s(Z) ds ≤ H^n(M ∩ cl Z) < ∞. Choose Borel h_Z with ν_s(Z) = h_Z(s) off a Borel null set N_Z. Let N₀ be a Borel null set containing every N_Z (Z ∈ 𝒫) and every s with ν_s(C_j) = ∞ for some j.
  - The modified slices. Put ν'_s := ν_s for s ∉ N₀ and ν'_s := 0 for s ∈ N₀.
 - Measurability of s ↦ ν'_s.
  - For each j, let 𝒟_j be the family of Borel Z such that s ↦ ν'_s(Z ∩ C_j) is Borel. It contains 𝒫, since Z ∩ C_j ∈ 𝒫.
  - 𝒟_j is a Dynkin system: ν'_s(Z^c ∩ C_j) = ν'_s(C_j) − ν'_s(Z ∩ C_j) with ν'_s(C_j) < ∞, and countable disjoint unions give sums.
  - By the π–λ theorem (MeasurableSpace.induction_on_inter), 𝒟_j contains all Borel sets. Letting j → ∞ (monotone), s ↦ ν'_s(Z) is Borel for every Borel Z.
  - By simple-function approximation and monotone convergence, s ↦ ∫ g dν'_s is Borel for every Borel g ≥ 0, and ∫_M g dH^n = ∫_L ∫ g dν'_s ds, since ν' = ν off a null set.
 - Joint measurability. For B ⊆ L × ℝ^P and v ∈ L, write B_v := {x : (v, x) ∈ B}.
  - Let 𝒞 be the family of Borel B ⊆ L × ℝ^P such that (s, v) ↦ ν'_s(B_v ∩ C_j) is Borel on L × L for every j.
  - 𝒞 contains the rectangles A × Z (A, Z Borel), for which the function is 1_A(v)·ν'_s(Z ∩ C_j). It is a Dynkin system by the same complement/disjoint-union argument.
  - By the π–λ theorem, 𝒞 contains all Borel B. Letting j → ∞, (s, v) ↦ ν'_s(B_v) is Borel. No kernel API is needed.
  - Applying this to B' and composing with the Borel map (s, v) ↦ (s + v, v) shows that (s, v) ↦ ν'_{s+v}(B'_v) is Borel.
 - Tonelli. For each v: ∫_L ν'_s(B_v) ds = H^n(M ∩ B_v) = 0, and ∫_L ν'_{s+v}(B'_v) ds = ∫_L ν'_t(B'_v) dt = H^n(M ∩ B'_v) = 0, using translation invariance of H^d⌞L. By Tonelli on L × L, for a.e. s: for a.e. v, ν'_s(B_v) = 0 and ν'_{s+v}(B'_v) = 0.
 - Choice of t₀. Fix t₀ ∈ 𝒯 ∖ N₀ with this property. Let V₀ be the full-measure set of v with ν_{t₀}(B_v) = 0, ν'_{t₀+v}(B'_v) = 0 and t₀ + v ∈ 𝒯 ∖ N₀; it has full measure since 𝒯 ∖ N₀ − t₀ is conull.
 - Consequence. Let v ∈ V₀ and t := t₀ + v. Then Γ(x + v) = Γ(x) for H^m-a.e. x ∈ M_{t₀}, and Γ(z − v) = Γ(z) for H^m-a.e. z ∈ M_t. For z ∈ p⁻¹(t) we have 1_M(z) = 1_{M_t}(z) and 1_M(z − v) = 1_{M_{t₀}}(z − v). Since ζ = ξ̃∘lift, the data (1_{M_t}θ, 1_{M_t}θζ) and z ↦ (1_{M_{t₀}}θ, 1_{M_{t₀}}θζ)(z − v) agree H^m-a.e. on M_t ∪ (M_{t₀} + v); both vanish off this set. By translation invariance of H^m:
 (★) R_t.action(γ) = R_{t₀}.action(γ(· + v)) for every test m-form γ, and R_t.measure(A) = R_{t₀}.measure(A − v) for every Borel A.
8. (Definition of R₀ and S₀.)
 - R₀ := (M₀, θ₀, ζ₀) with M₀ := M_{t₀} − t₀, θ₀(y) := θ(y + t₀) and ζ₀(y) := ζ(y + t₀). It is an IMRep of dimension m: the translate of R_{t₀}, as in step 6.
 - By the accepted dtc_imrep_current, let S₀ ∈ 𝒟_m(ℝ^P) be a current represented by R₀. Then R₀.action(γ) = R_{t₀}.action(γ(· − t₀)) and μ₀(A) := R₀.measure(A) = R_{t₀}.measure(A + t₀).
 (a) M₀ ⊆ {y : p(y + t₀) = t₀} = {y : p(y) = 0} = L^⊥, since p(t₀) = t₀. Hence μ₀(ℝ^P ∖ L^⊥) = 0.
 (b) spt S₀ ⊆ L^⊥. Let x ∉ L^⊥; L^⊥ is closed, so some ball W around x with compact closure misses L^⊥. Every test m-form γ with tsupport γ ⊆ W vanishes on M₀ ⊆ L^⊥, so S₀(γ) = ∫_{M₀} θ₀ζ₀(γ) dH^m = 0. Hence W lies in the zero region of S₀ and x ∉ spt S₀.
 (c) Measure identity. For Borel A, μ(A) = ∫_L R_t.measure(A) dt (step 5). For a.e. t, namely t = t₀ + v with v ∈ V₀, (★) gives R_t.measure(A) = R_{t₀}.measure(A − v) = μ₀(A − t) = R₀.measure((fun y => t + y)⁻¹' A). Hence μ(A) = ∫⁻ t in L, R₀.measure((fun y => t + y)⁻¹' A) ∂μHE[d].
 (d) Product formula. Let ω be a test n-form. By step 5, S(ω) = ∫_L R_t.action(♭ω) dt. For t = t₀ + v with v ∈ V₀, (★) gives R_t.action(♭ω) = R_{t₀}.action((♭ω)(· + v)) = R₀.action(y ↦ ♭ω(y + t₀ + v)) = S₀(y ↦ ♭(ω(t + y))). By step 1 this equals currentEval S₀ (fun y => ♭(ω(t + y))). The integrands agree a.e. in t, so S(ω) = ∫_L currentEval S₀ (fun y => ♭(ω(t + y))) dH^d(t). ∎

## Key steps

1. Write ξ = f_1∧⋯∧f_d∧ζ on the good set, with ζ := ξ̃∘lift a measurable unit orientation of T_x∩L^⊥ and ξ(α) = ζ(♭α).
2. The child spine_coarea slices M by p: for a.e. t, R_t = (M ∩ p⁻¹(t), θ, ζ) is an m-dimensional IMRep, S(ω) = ∫_L R_t.action(♭ω) dt and μ(A) = ∫_L R_t.measure(A) dt.
3. Translation invariance and the accepted uniqueness lemmas make the data (1_Mθ, 1_Mθξ̃) L-invariant H^n-a.e.
4. Tonelli on L × L, with a measurable version of the slice kernel, picks a base slice t₀ with R_{t₀+v} = τ_{v#}R_{t₀} for a.e. v.
5. R₀ := R_{t₀} − t₀ and S₀ := its current give μ₀ concentrated on L^⊥, spt S₀ ⊆ L^⊥, μ = ∫_L μ₀(· − t) dt and S(ω) = ∫_L S₀(♭ω(t + ·)) dt.

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
