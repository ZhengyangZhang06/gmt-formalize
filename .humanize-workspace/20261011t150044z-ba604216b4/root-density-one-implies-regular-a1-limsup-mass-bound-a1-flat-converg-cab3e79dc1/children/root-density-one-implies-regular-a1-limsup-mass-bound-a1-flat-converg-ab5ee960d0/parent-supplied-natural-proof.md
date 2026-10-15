# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, proof of the Deformation Theorem 5.1, displays (26)–(37) (chapter-06.txt, from "Now let F be a given face of L_n" to (37)), in the form of step 7 of the parent proof: since Q is integer multiplicity, (26)–(28) are read off from an IMRep of Q (using (IMC)(a)) instead of the constancy-theorem argument for general currents, and (33) follows from Hⁿ(L_{n−1}) = 0. Dependencies: (C1) = the reused sibling dor_imrep_massOn_eq_measure_and_support; (IMC) = the reused sibling cmc_imRep_locality_restrict_sub; CP = the sibling dor_lmb_fcd_cube_poincare (the BV Poincaré inequality with integer median on the unit cube, Simon Ch. 2, 2.7 with (31), (35)).

Notation. n := m + 1 < P. A pair p = (z, ι) ∈ ℤ^P × (Fin n → Fin P) with ι strictly increasing determines the closed unit face F_p := {x : z_i ≤ x_i ≤ z_i + 1 for i ∈ range ι, x_i = z_i otherwise} and the open face F_p° (strict inequalities); e_ι := (e_{ι(0)}, …, e_{ι(m)}) and V_ι := span e_ι. L_n is the statement's set {x : at least P − n coordinates are integers}, L_{n−1} := {x : at least P − n + 1 coordinates are integers}. All currents are on univ; Q is IM, vanishes off L_n ∩ K (K compact) and M(∂Q) < ∞.

1. Face geometry. (a) φ_p(y) := z + Σ_k y_k e_{ι(k)} is an isometric embedding ℝⁿ → ℝ^P with φ_p([0,1]ⁿ) = F_p and φ_p((0,1)ⁿ) = F_p°; μHE[n] is preserved by isometries and equals Lebesgue measure on ℝⁿ (Mathlib Isometry.euclideanHausdorffMeasure_image and the characterization of μHE[n] on Euclid n), so Hⁿ(F_p) = Hⁿ(F_p°) = 1, Hⁿ(F_p ∖ F_p°) = 0, and ∫_{F_p} f dHⁿ = ∫_{F_p°} f dHⁿ = ∫_{(0,1)ⁿ} f∘φ_p dy for integrable f. (b) Every point of L_n ∖ L_{n−1} lies in exactly one open face F_p° (its non-integer coordinates, exactly n of them, give range ι, and z_i is the integer part of x_i); distinct open faces are disjoint; and L_{n−1} is a countable union of (n − 1)-dimensional faces, each the isometric image of [0,1]^{n−1}, so Hⁿ(L_{n−1}) = 0. (c) diam F_p = √n ≤ √P; F_p is compact; only finitely many faces meet the compact K. (d) L_n ∖ F_p° is closed (it is (F_p ∖ F_p°) ∪ ⋃_{p'≠p} F_{p'}, a locally finite union of closed sets).

2. The measure of Q (parent (C1); Simon (28)). Let R_Q = (M, θ, ξ) be an IMRep of Q and μ_Q := R_Q.measure = θHⁿ⌞M. By (C1), μ_Q(W) = M_W(Q) for open W. Every admissible form for the open set W₀ := ℝ^P ∖ (L_n ∩ K) has tsupport disjoint from L_n ∩ K, so Q vanishes on it and μ_Q(W₀) = M_{W₀}(Q) = 0. Since θ ≥ 1 on M, Hⁿ(M ∖ (L_n ∩ K)) = 0; with 1(b), Hⁿ-almost every x ∈ M lies in F_p° for exactly one p, and then F_p ∩ K ≠ ∅. Also μ_Q(ℝ^P) = μ_Q(K) ≤ ∫_{M∩K}θ dHⁿ < ∞ (local integrability of the IMRep on the compact K), so M(Q) < ∞, and Hⁿ(M ∩ K') < ∞ for every compact K'.

3. Orientation on a face (Simon (26)–(27)). Fix p with F_p ∩ K ≠ ∅ and let M_p := M ∩ F_p° (Borel). By (IMC)(a) (with M_p ⊆ M ⊆ ℝ^P, U = univ, Hⁿ(M ∩ K') < ∞), for Hⁿ-a.e. x ∈ M_p the approximate tangent spaces of M and of M_p at x agree. M_p = φ_p(A) with A ⊆ (0,1)ⁿ Borel; at every Lebesgue density point y of A, M_p has approximate tangent space V_ι at φ_p(y) (for f ∈ C_c(ℝ^P), the blow-ups satisfy ∫_{(M_p − x)/λ} f dHⁿ = ∫_{(A − y)/λ} f(Σ_k w_k e_{ι(k)}) dw → ∫_{ℝⁿ} f(Σ_k w_k e_{ι(k)}) dw = ∫_{V_ι} f dHⁿ by the density-one property and dominated convergence), and almost every point of A is a density point. At Hⁿ-a.e. x ∈ M the IMRep field `orients` gives a subspace Q with HasApproximateTangentSpaceAt n M x Q and ξ(x) a unit orientation of Q, and approximate tangent spaces are unique (the defining limits determine the measure Hⁿ⌞Q, hence Q; accepted DAG theorem dpf_itt_approxTangentPlane_eq, whose two-line argument is reproduced here). Hence for Hⁿ-a.e. x ∈ M_p, ξ(x) is a unit orientation of V_ι; since e_ι is an orthonormal basis of V_ι and two orthonormal frames of V_ι differ by an orthogonal matrix of determinant ±1, ξ(x)(α) = ε(x)α(e_ι) for all n-covectors α, with ε(x) ∈ {1, −1}. Define θ_p : ℝ^P → ℤ by θ_p(x) := ε(x)θ(x) at such points x ∈ M_p (ε(x) = ξ(x)(dx^{ι(0)} ∧ ⋯ ∧ dx^{ι(m)}) is Hⁿ⌞M-a.e. equal to a Borel function since ξ is a.e. strongly measurable; replace ε and the set of points where ξ(x) orients V_ι by Borel versions agreeing a.e. — integrals, actions and measures are unchanged) and θ_p := 0 elsewhere. Then for every n-form ω (bounded and Borel, in particular every test form)
 (27) ∫_{M_p} θ ξ(ω) dHⁿ = ∫_{F_p°} θ_p(x) ω(x)(e_ι) dHⁿ(x), and ∫_{F_p°} |θ_p| dHⁿ = μ_Q(F_p°).
 Let 𝒫 be the finite set of p with F_p ∩ K ≠ ∅. By step 2 and (27):
 (33) Q(ω) = Σ_{p∈𝒫} ∫_{F_p°} θ_p ω(e_ι) dHⁿ for every test n-form ω, and M(Q) = μ_Q(ℝ^P) = Σ_{p∈𝒫} ∫_{F_p°}|θ_p| dHⁿ (28, first part).

4. Variation bound (Simon (28), second part, by the argument of 2.34–2.35). For p ∈ 𝒫 let V_p := {x : infDist x F_p° < infDist x (L_n ∖ F_p°)} (open; the V_p are pairwise disjoint: if x ∈ V_p ∩ V_{p'} with p ≠ p', then F_{p'}° ⊆ L_n ∖ F_p° and F_p° ⊆ L_n ∖ F_{p'}° give infDist x F_p° < infDist x F_{p'}° < infDist x F_p°; and V_p ∩ L_n ⊆ F_p°, since x ∈ L_n ∖ F_p° gives infDist x (L_n ∖ F_p°) = 0). Let u_p := θ_p∘φ_p on Q₁ := (0,1)ⁿ: integer-valued, with ∫_{Q₁}|u_p| = ∫_{F_p°}|θ_p| dHⁿ < ∞ (step 1(a)).
 Claim: for every C^∞ g : ℝⁿ → ℝⁿ with compact support in Q₁ and |g| ≤ 1, ∫_{Q₁} u_p div g ≤ M_{V_p}(∂Q).
 Proof. The compact set G := φ_p(spt g) ⊆ F_p° has positive distance 3δ from the closed set L_n ∖ F_p° (1(d)). Write x_⊥ for the coordinates (x_i)_{i∉range ι} and π(x) := (x_{ι(k)} − z_{ι(k)})_k ∈ ℝⁿ. Let η ∈ C^∞(ℝ), 0 ≤ η ≤ 1, η = 1 on (−∞, δ²/4], η = 0 on [δ², ∞), χ(x) := η(|x_⊥ − z_⊥|²), and define the (n − 1)-form
 ω(x) := χ(x) Σ_{l=0}^{m} (−1)^l g_l(π(x)) dx^{ι(0)} ∧ ⋯ ∧ (dx^{ι(l)} omitted) ∧ ⋯ ∧ dx^{ι(m)}.
 ω is C^∞ with compact support in {π(x) ∈ spt g, |x_⊥ − z_⊥| ≤ δ}, whose points are within δ of G, hence satisfy infDist x F_p° ≤ δ < 2δ ≤ infDist x (L_n ∖ F_p°); so tsupport ω ⊆ V_p. Its coefficients on distinct basis covectors are ±χ g_l, so its Euclidean coefficient norm is χ|g| ≤ 1: ω is admissible for M_{V_p}(∂Q). On the set {|x_⊥ − z_⊥| < δ/2}, where χ ≡ 1, dω = Σ_l (∂_l g_l)(π(x)) dx^{ι(0)} ∧ ⋯ ∧ dx^{ι(m)} = (div g)(π(x)) dx^ι; in particular dω(x)(e_ι) = div g(π(x)) on F_p°. Since tsupport dω ⊆ tsupport ω ⊆ V_p and V_p ∩ F_{p'}° = ∅ for p' ≠ p, (33) gives ∂Q(ω) = Q(dω) = ∫_{F_p°} θ_p (div g)∘π dHⁿ = ∫_{Q₁} u_p div g dy (1(a)). Hence ∫_{Q₁} u_p div g = ∂Q(ω) ≤ M_{V_p}(∂Q).
 Moreover Σ_{p∈𝒫} M_{V_p}(∂Q) ≤ M(∂Q): given admissible ω_p for V_p (p ∈ 𝒫), ω := Σ_p ω_p is admissible for ℝ^P (the supports are disjoint, so |ω(x)| = |ω_p(x)| ≤ 1 at points of tsupport ω_p and 0 elsewhere) and ∂Q(ω) = Σ_p ∂Q(ω_p); take suprema. In particular each M_{V_p}(∂Q) ≤ M(∂Q) < ∞.

5. Integer medians (Simon (31), (32), (35)). Let c_cp > 0 be the constant of CP for m. For p ∈ 𝒫 apply CP to u := u_p and V := (M_{V_p}(∂Q)).toReal (finite by step 4; hypothesis (H) of CP holds by the claim of step 4, since M_{V_p}(∂Q) = ENNReal.ofReal V): there is β_p ∈ ℤ with
 (32) ∫_{F_p°}|θ_p − β_p| dHⁿ = ∫_{Q₁}|u_p − β_p| ≤ c_cp·M_{V_p}(∂Q), and (35) |β_p| ≤ 2∫_{Q₁}|u_p| = 2∫_{F_p°}|θ_p| dHⁿ.

6. The chain P (Simon (34)–(36)). Let s := {p ∈ 𝒫 : β_p ≠ 0} (finite, each ι strictly increasing), β(p) := β_p for p ∈ s and β(p) := 0 otherwise, and Pc(ω) := Σ_{p∈s} β_p ∫_{F_p} ω(x)(e_ι) dHⁿ(x). Pc is linear and |Pc(ω)| ≤ (Σ_{p∈s}|β_p|)·sup_x|ω(x)(e_ι)| (Hⁿ(F_p) = 1), so it is sequentially continuous on test forms: Pc ∈ 𝒟_n(ℝ^P), and it satisfies the face formula of the statement by definition. By 1(a), ∫_{F_p} = ∫_{F_p°}, so with (33), for every ω:
 (29) (Q − Pc)(ω) = Σ_{p∈𝒫} ∫_{F_p°} (θ_p − β_p) ω(e_ι) dHⁿ (β_p = 0 for p ∈ 𝒫 ∖ s).
 Integrality of Q − Pc. Let M' := ⋃_{p∈𝒫} {x ∈ F_p° : θ_p(x) ≠ β_p} (Borel, θ_p being the Borel version of step 3; a disjoint union), θ'(x) := |θ_p(x) − β_p| and ξ'(x)(α) := sign(θ_p(x) − β_p)·α(e_ι) for x ∈ F_p° ∩ M' (θ' := 0, ξ' := 0 off M'). This is an IMRep in univ: M' is Borel and countably n-rectifiable (contained in finitely many n-planes); θ' is a Borel positive integer on M' and ∫_{M'}θ' dHⁿ ≤ Σ_p(∫|θ_p| + |β_p|) < ∞; ξ' is Borel; and for Hⁿ-a.e. x ∈ M' ∩ F_p°, M' has approximate tangent space V_ι at x (density points as in step 3, using (IMC)(a) for M' ∩ F_p° ⊆ M'), which ±(α ↦ α(e_ι)) orients (e_ι is orthonormal). Its action is θ'ξ'(ω) = (θ_p − β_p)ω(e_ι) on F_p° ∩ M' and 0 elsewhere, so by (29) it represents Q − Pc: Q − Pc is IM.
 Mass (34). By (C1) for this IMRep: M(Q − Pc) = ∫_{M'}θ' dHⁿ = Σ_{p∈𝒫} ∫_{F_p°}|θ_p − β_p| dHⁿ ≤ c_cp Σ_p M_{V_p}(∂Q) ≤ c_cp·M(∂Q) (steps 4, 5).
 Coefficients (36). Σ_{p∈s}|β_p| ≤ Σ_{p∈𝒫} 2∫_{F_p°}|θ_p| dHⁿ = 2M(Q) (steps 3, 5).
 Supports. For p ∈ s ⊆ 𝒫, F_p meets K, so every point of F_p is within diam F_p = √n ≤ √P of a point of K: F_p ⊆ cthickening(√P, K). If tsupport ω is disjoint from cthickening(√P, K), then ω vanishes on F_p° for every p ∈ 𝒫, so (Q − Pc)(ω) = 0 by (29).

7. Conclusion. With c := max(c_cp, 2) ≥ 0 (depending only on m, hence on P and m), s, β and Pc satisfy every conclusion: StrictMono, the face formula, IM(Q − Pc), M(Q − Pc) ≤ c·M(∂Q), Σ|β_p| ≤ c·M(Q), the inclusions F_p ⊆ cthickening(√P, K) and the vanishing of Q − Pc off cthickening(√P, K). ∎

## Key steps

1. Unit faces are isometric images of [0,1]ⁿ (Hⁿ(F) = 1, boundaries null), open faces are disjoint, Hⁿ(L_{n−1}) = 0, finitely many faces meet K.
2. (C1): the IMRep of Q is carried (up to null sets) by the open faces meeting K; (IMC)(a) and density points give orientation ±e_ι there, so Q = Σ_F θ_F[[F°]] with M(Q) = Σ∫|θ_F| ((26)–(28), (33)).
3. Testing ∂Q with (n−1)-forms built from g ∈ C_c^∞(Q₁; ℝⁿ) and a normal cut-off inside V_F shows ∫ u_F div g ≤ M_{V_F}(∂Q), and Σ_F M_{V_F}(∂Q) ≤ M(∂Q).
4. CP gives integer medians β_F with ∫|θ_F − β_F| ≤ c_cp M_{V_F}(∂Q) and |β_F| ≤ 2∫|θ_F| ((31), (32), (35)).
5. Pc := Σ β_F[[F]]; Q − Pc = Σ(θ_F − β_F)[[F°]] is IM with M(Q − Pc) ≤ c_cp M(∂Q) and Σ|β_F| ≤ 2M(Q); faces with β_F ≠ 0 meet K, giving the support clauses ((34), (36)).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project b4d606db, mathlib 25730c7c)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `rg -l -i "latticeFace|DeformationTheorem|deformation theorem|skeleton|retraction" local-references/123e8435b4a2469b/project -g "*.lean" (only GMT/Ch06/Contract.lean and GMT/Ch06/Submission.lean)`
- `rg -n "latticeFace|def DeformationTheorem|IsLatticeChain|pushforward|homotopy|Poincar" local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `rg -n "theorem hausdorffMeasure_smul₀|theorem integral_map_equiv|theorem restrict_map|exists_disjoint_subfamily_covering_enlargement|theorem extend_real|theorem cthickening_cthickening_subset|theorem cthickening_eq_biUnion_closedBall|theorem lipschitz_infDist_pt|theorem ae_differentiableAt" local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -c for extend_pi, integral_lineDeriv_mul_eq, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, image_of_continuousOn_injOn, ae_convolution_tendsto_right_of_locallyIntegrable, euclideanHausdorffMeasure_image, hausdorffMeasure_image_le, measure_compl_support, measurable_fderiv in Mathlib (all present)`
- `grep -n "theorem integral_lineDeriv_mul_eq" Mathlib/Analysis/Calculus/Rademacher.lean; sed -n 1,140p Mathlib/Geometry/Euclidean/Volume/Measure.lean (μHE[d], isometry invariance)`
- `grep -n "^def |^theorem" SimonGMT Chapter06/{Product,GeometricPointProduct,AffineCurrentPushforward,Currents,Mass,CurrentLocalEquality,Forms}.lean (only affine push-forward and point products; no Lipschitz push-forward, no [[(0,1)]] × T, no homotopy formula)`
- `grep -rn "theorem [a-zA-Z_.]*area" .lake/packages/simongmt/Poincare/SimonGMT (Chapter02 area formulas: injective_area_formula_lipschitz, area_image_criticalSet_eq_zero, ...)`
- `grep -n "def HasApproximateTangentSpaceAt|def CountablyRectifiable|def blowUpMap" SimonGMT/Chapter03/Rectifiable.lean`
- `rg -c exteriorDerivativeOn_pullbackFormWithin, exteriorDerivative_affinePullbackForm, WeaklyConvergesOn.boundary, countablyRectifiable_of_measure_zero in SimonGMT (present)`
- `python3 -I scans of dag.json (1366 nodes, 2026-10-13T14:15Z): statuses and frozen types of dor_imrep_massOn_eq_measure_and_support, cmc_imRep_locality_restrict_sub (accepted), dor_lmb_fc_im_series (decomposing), dor_lmb_slicing_lipschitz (speculative-ready), accepted dpf_*/ptd_*/pit_*/dtc_* helpers; byte-identical types of cmcdt_skeleton_retraction, cmcdt_good_center, dimred_mbl_dt_*; freshness of the dor_lmb_fcd_* names`
- `python3 -I parse of nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/decomposition-v2.json and nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/decomposition-v2.json`
- `sed -n 340,960p and 1400,1965p book/chapter-06.txt; sed -n 470,700p book/chapter-02.txt`
- `sed -n 6660,6760p and 3210,3260p /runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py (_existing_lean_name_problem, accepted-child overlay scoping)`
- `lake env lean /tmp/dfm-decomp/lean/Challenge_*.lean (12 exact comparator challenges), AllProps.lean, Assembly.lean and UnitAssembly.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/GeometricPointProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-cab3e79dc1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `/tmp/dfm-decomp/lean/Assembly.lean`
- `/tmp/dfm-decomp/lean/UnitAssembly.lean`
- `/tmp/dfm-decomp/lean/AllProps.lean`

Snapshot: project b4d606db, mathlib 25730c7c; the snapshot Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Neither the snapshot nor SimonGMT contains a proved Deformation Theorem, Lemma 5.4, a Lipschitz push-forward of currents, the product [[(0,1)]] × T, or the homotopy formula: SimonGMT Chapter06 provides only affine push-forwards and point products (plus currents, boundary, massOn, support, weak convergence with lower semicontinuity); Chapter02 provides area formulas for Lipschitz maps; Chapter03 the literal approximate-tangent-space definition. The snapshot's GMT/Ch06/Contract.lean has only sorry-frozen latticeFace/IsLatticeChain/DeformationTheorem definitions (the same unit and ρ-cells as the child face formulas), not imported by GMT.Ch07.Submission. Every Mathlib lemma cited in the child proofs exists in the pinned snapshot (Vitali covering, cthickening lemmas, lipschitz_infDist_pt, integral_map_equiv, MeasurableEquiv.restrict_map, hausdorffMeasure_smul₀, integral_lineDeriv_mul_eq, Rademacher, measurable_fderiv, convolution a.e. convergence, Isometry.euclideanHausdorffMeasure_image, measure_compl_support). Reuse: dor_imrep_massOn_eq_measure_and_support and cmc_imRep_locality_restrict_sub are accepted with byte-identical frozen types (standard axioms per acceptance); dor_lmb_fc_im_series (decomposing) and dor_lmb_slicing_lipschitz (speculative-ready) are passed as exact-type antecedents. Lean: all 12 child types compile as exact comparator challenges; parent_assembly and unit_assembly compile with axioms [propext, Classical.choice, Quot.sound].
