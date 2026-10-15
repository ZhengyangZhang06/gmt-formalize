# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.face_currents-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 4 (faces: products of Y₀ with the faces of the cube, via the frames f^(a)) and 5 (the face current E'_r = Σ_a (−1)^{a−1}(τ_{rf_a}P_a − τ_{−rf_a}P_a), integer multiplicity by (F4) and translation, with M(E'_r) ≤ 2d(2r)^{d−1}M(Y₀)) of the selected proof, with the frame indexed from 0. Here the translation is applied to Y before taking the product (P^{a,±} = [[Q'_a]] ×_{g^(a)} τ_{±rg_a}Y), which gives the same action.
Siblings used: product_current (Submission.idtp_fons_cs_sos_product_current), mass_triangle (Submission.lcmp_massOn_le_add_of_eval_eq), frame_measure (Submission.dimred_cs_sos_mt_frame_measure). Accepted results cited by name (dependencies of the selected node): dtc_imrep_current (every IMRep represents a current), imrep_represents_massOn_eq_measure (F1: M_W(T) = R.measure(W) for open W), rsd_isIntegerMultiplicity_int_combination (F4).
Notation: σ_Y := R_Y.measure; ω̂ := (ω : DifferentialForm (Euclid P) n'); M(T) := T.mass = T.massOn ℝ^P.

Step 1 (translates of integer multiplicity currents). Let l ∈ ℕ, A ∈ 𝒟_l(ℝ^P) with an IMRep R_A = (M, θ, ξ), and v ∈ ℝ^P. Then there are A^v ∈ 𝒟_l(ℝ^P) and an IMRep R^v representing A^v such that (a) currentEval A^v φ = currentEval A (y ↦ φ(y + v)) for every l-form φ, and (b) R^v.measure(C) = R_A.measure((y ↦ y + v)⁻¹'C) for every Borel C.
Proof. τ(x) := x + v is an isometry of ℝ^P onto itself (an IsometryEquiv), so it preserves μHE[l]: H^l(τ(D)) = H^l(D) for every D, and ∫ f d(H^l⌞τ(D)) = ∫ f∘τ d(H^l⌞D) (IsometryEquiv.measurePreserving_euclideanHausdorffMeasure, Isometry.euclideanHausdorffMeasure_image). Put R^v := (M', θ', ξ') with M' := τ(M) = {x : x − v ∈ M}, θ'(x) := θ(x − v), ξ'(x) := ξ(x − v). The IMRep axioms hold:
 - M' is Borel (preimage of M under the continuous map x ↦ x − v) and M' ⊆ ℝ^P.
 - M' is countably l-rectifiable: if M ⊆ M₀ ∪ ⋃_i range F_i with H^l(M₀) = 0 and F_i Lipschitz (SimonGMT CountablyRectifiable), then M' ⊆ τ(M₀) ∪ ⋃_i range(τ ∘ F_i) with H^l(τ(M₀)) = 0 and τ ∘ F_i Lipschitz.
 - θ' is measurable, ℕ-valued and θ' ≥ 1 on M'; for compact K, ∫_{M'∩K} θ' dH^l = ∫_{M∩(K − v)} θ dH^l < ∞ (change of variables under τ; K − v is compact).
 - ξ' is a.e.-strongly measurable for H^l⌞M', as the composition of ξ (a.e.-strongly measurable for H^l⌞M) with the measure-preserving map x ↦ x − v from H^l⌞M' to H^l⌞M.
 - Tangent planes: for x ∈ ℝ^P and r' > 0, blowUpMap (x + v) r' '' M' = {r'⁻¹((y + v) − (x + v)) : y ∈ M} = blowUpMap x r' '' M, and SimonGMT HasApproximateTangentSpaceAt l N z Q depends on (N, z) only through the sets blowUpMap z r' '' N; so HasApproximateTangentSpaceAt l M' (x + v) Q ⟺ HasApproximateTangentSpaceAt l M x Q. τ maps H^l-null subsets of M onto H^l-null subsets of M', so for H^l-a.e. x' ∈ M', with x := x' − v ∈ M good for R_A.orients, ξ'(x') = ξ(x) is a unit orientation of an approximate tangent plane of M' at x'.
 Let A^v be a current represented by R^v (dtc_imrep_current). If φ is a test form, so is φ(· + v), and A^v(φ) = R^v.action(φ) = ∫_{M'} θ(x − v)·ξ(x − v)(φ(x)) dH^l(x) = ∫_M θ(y)·ξ(y)(φ(y + v)) dH^l(y) = R_A.action(φ(· + v)) = A(φ(· + v)); this is (a) for test forms. If φ is not a test form, then neither is φ(· + v) (translation preserves smoothness, and compactness of the support in both directions), and both sides of (a) are 0. For (b): R^v.measure(C) = ∫_{M'∩C} θ' dH^l = ∫_{M∩(C − v)} θ dH^l = R_A.measure((y ↦ y + v)⁻¹'C).

Step 2 (the frames g^(a)). g^(a) = g ∘ a.succAbove is orthonormal (the restriction of an orthonormal family along the injective map a.succAbove). G_a ⊆ G, hence G^⊥ ⊆ G_a^⊥. Moreover ⟨g_a, g_{a.succAbove c}⟩ = 0 for all c (a.succAbove c ≠ a), so g_a ∈ G_a^⊥.

Step 3 (the 2(j + 1) face currents). Fix a ∈ Fin (j + 1) and ε ∈ {+1, −1}, and put v := ε·r·g_a. Let Y^{a,ε} := Y^v with IMRep R^{a,ε} := R^v (Step 1, with A := Y, R_A := R_Y, l := m + 1). Its measure is carried by G_a^⊥: R^{a,ε}.measure(ℝ^P ∖ G_a^⊥) = σ_Y({y : y + v ∉ G_a^⊥}) = σ_Y(ℝ^P ∖ G_a^⊥) ≤ σ_Y(ℝ^P ∖ G^⊥) = 0, because v ∈ G_a^⊥ (Step 2) and G^⊥ ⊆ G_a^⊥. Apply product_current with k := j, m' := m + 1 > 0, n', h := h₂, the orthonormal frame g^(a), E := Q'_a (closed, hence Borel, and Q'_a ⊆ G_a), A := Y^{a,ε} and R_A := R^{a,ε}. It gives P^{a,ε} ∈ 𝒟_{n'}(ℝ^P) and an IMRep R_{a,ε} representing it with
 (i) R_{a,ε}.measure(C) = ∫_{Q'_a} R^{a,ε}.measure((y ↦ s + y)⁻¹'C) dH^j(s) for every Borel C, and
 (ii) P^{a,ε}(ω) = ∫_{Q'_a} currentEval Y^{a,ε} (y ↦ flatF a(ω̂(s + y))) dH^j(s) for every map flatF a with the identity for (g^(a), h₂) and every test n'-form ω.
By Step 1 (a), currentEval Y^{a,ε} (y ↦ flatF a(ω̂(s + y))) = currentEval Y (y ↦ flatF a(ω̂(s + (y + v)))) = currentEval Y (y ↦ flatF a(ω̂((s + v) + y))), and s + v = s + r·g_a for ε = 1, s + v = s − r·g_a for ε = −1. Hence
 P^{a,+}(ω) = ∫_{Q'_a} currentEval Y (y ↦ flatF a(ω̂(s + r·g_a + y))) dH^j(s) and P^{a,−}(ω) = ∫_{Q'_a} currentEval Y (y ↦ flatF a(ω̂(s − r·g_a + y))) dH^j(s).

Step 4 (mass of one face). By imrep_represents_massOn_eq_measure with W = ℝ^P, Step 3 (i) with C = ℝ^P and Step 1 (b): M(P^{a,ε}) = R_{a,ε}.measure(ℝ^P) = ∫_{Q'_a} R^{a,ε}.measure(ℝ^P) dH^j = H^j(Q'_a)·σ_Y(ℝ^P). Q'_a is exactly the closed box of radius r > 0 of the orthonormal j-frame g^(a), so H^j(Q'_a) = ENNReal.ofReal((2r)^j) by frame_measure (ii). Thus M(P^{a,ε}) = ENNReal.ofReal((2r)^j)·σ_Y(ℝ^P).

Step 5 (summation). For currents A, B ∈ 𝒟_{n'}(ℝ^P) and c ∈ ℝ, the functional ω ↦ A(ω) + c·B(ω) is again a current (it is linear, and sequentially continuous as a combination of sequentially continuous functionals). Let D_a be the current ω ↦ P^{a,+}(ω) − P^{a,−}(ω); it is integer multiplicity by rsd_isIntegerMultiplicity_int_combination (p₁ = 1, p₂ = −1, U = ℝ^P open), and M(D_a) ≤ M(P^{a,+}) + M(P^{a,−}) = 2·ENNReal.ofReal((2r)^j)·σ_Y(ℝ^P) by mass_triangle (G := ℝ^P, c = −1) and Step 4. Put c₀ := 2·ENNReal.ofReal((2r)^j)·σ_Y(ℝ^P). Claim: for every finite set s ⊆ Fin (j + 1) there is an integer multiplicity E_s ∈ 𝒟_{n'}(ℝ^P) with E_s(ω) = Σ_{a∈s} (−1)^a·(P^{a,+}(ω) − P^{a,−}(ω)) for every test form ω and M(E_s) ≤ card(s)·c₀. Proof of the claim by Finset.induction_on (a statement about existence, so no definition by recursion is needed):
 - s = ∅: take E_∅ := 0. It is integer multiplicity (rsd_isIntegerMultiplicity_int_combination with p₁ = p₂ = 0 and T₁ = T₂ := P^{0,+}), its action is the empty sum 0, and M(0) = 0 (every value in the supremum defining the mass is ofReal 0).
 - s ↦ insert a s with a ∉ s: given E_s, take E_{insert a s} := (ω ↦ E_s(ω) + (−1)^a·D_a(ω)). It is integer multiplicity (rsd_isIntegerMultiplicity_int_combination with p₁ = 1, p₂ = (−1)^a ∈ ℤ); its action is Σ_{b ∈ insert a s} (−1)^b·(P^{b,+}(ω) − P^{b,−}(ω)) (Finset.sum_insert); and M(E_{insert a s}) ≤ M(E_s) + M(D_a) ≤ card(s)·c₀ + c₀ = card(insert a s)·c₀ by mass_triangle (G := ℝ^P, c = (−1)^a, |c| = 1).
Let E' := E_{Finset.univ}. It is integer multiplicity, M(E') ≤ (j + 1)·c₀ = ENNReal.ofReal(2(j + 1)(2r)^j)·R_Y.measure(ℝ^P), and for every family flatF with the identity and every test form ω, E'(ω) = Σ_a (−1)^a·(P^{a,+}(ω) − P^{a,−}(ω)), which by Step 3 is the asserted sum. ∎

## Key steps

1. Translation of an integer multiplicity current: R^v = (M + v, θ(· − v), ξ(· − v)) is an IMRep (blow-up images and μHE are translation invariant) of a current A^v with currentEval A^v φ = currentEval A (φ(· + v)) and translated measure.
2. For v = ±r g_a ∈ G_a^⊥, τ_vY is carried by G_a^⊥, and product_current with the frame g ∘ a.succAbove and E = Q'_a gives face currents P^{a,±} with the face action.
3. M(P^{a,±}) = H^j(Q'_a)·μ_Y(ℝ^P) = (2r)^j μ_Y(ℝ^P) by F1, the product measure formula and frame_measure.
4. E' = Σ_a (−1)^a (P^{a,+} − P^{a,−}) is integer multiplicity (F4, induction) with M(E') ≤ 2(j + 1)(2r)^j μ_Y(ℝ^P) (mass_triangle).

## Reference use

### local-project

Queries:
- `cat manifest.json (project b4d606db1, mathlib 25730c7c); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `python3 over dag.json: split_off_spine nodes and statuses; ancestors and their depends_on; all 2101 accepted nodes dumped to /tmp/mt-decomp/accepted.txt and grepped for translate|massOn_le_add|measure_restrict|support|blowUp|hasDerivAt`
- `git show <candidate>:GMT/Ch07/Submission.lean for idtp_fons_cs_sos_product_current (4aa9ba8d), lcmp_massOn_le_add_of_eval_eq (c7dea4b8), dimred_cs_ti_translate_action_hasDerivAt (f899c748): declarations present, types byte-identical; product_current adds import Poincare.SimonGMT.Chapter02.AreaLipschitz`
- `read nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-60772a06fe/parent-supplied-natural-proof.md (parallel minimality_transfer with the identical frozen type, product construction moved to product_current) and the accepted proofs of the three reused nodes`
- `grep -n over runtime.py (_dependency_problem, _existing_lean_name_problem, _overlay_accepted_children) and inherited.py (cited_inherited: ancestor dependencies cited by exact Lean name)`
- `grep -n over SimonGMT Chapter06/{Currents,Mass,Forms,CurrentLocalEquality}.lean and Chapter03/Rectifiable.lean: GeometricCurrentOn.boundary(_apply), exteriorDerivativeTestOn, CurrentOn.boundary_boundary, massOn/mass/massOn_mono, zeroRegion/support, exteriorDerivative_apply, CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt`
- `grep -n over snapshot mathlib Geometry/Euclidean/Volume/Measure.lean: EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.map_euclideanHausdorffMeasure, Isometry.euclideanHausdorffMeasure_image, IsometryEquiv.measurePreserving_euclideanHausdorffMeasure`
- `rg -n over snapshot mathlib: PiLp.volume_preserving_toLp, Real.volume_pi_closedBall, Real.volume_pi_ball, measurePreserving_piFinSuccAbove, intervalIntegral.integral_eq_sub_of_hasDerivAt, continuousAt_of_dominated, setIntegral_sdiff (integral_diff deprecated alias), measure_add_measure_compl, withDensity_apply, Measure.restrict_restrict, Measure.integrableOn_of_bounded, Fin.append_left, fderiv_comp_add_left, finrank_span_eq_card, Submodule.eq_of_le_of_finrank_eq, ENNReal.le_of_add_le_add_left, lintegral_indicator_const, Fin.removeNth`
- `rg -n "Cartesian product of currents|slice of a current|cartesianProduct" snapshot mathlib (no match)`
- `lake env lean /tmp/mt-decomp/check/{Types,Assembly,CubeCycle,CompMass}.lean (Lean v4.35.0-rc3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-7f270cb1eb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-7f270cb1eb/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-60772a06fe/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-da13543666/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-mass-triangle-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-translation-inv-37aaf335d9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/inherited.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/models.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/mt-decomp/check/Types.lean`
- `/tmp/mt-decomp/check/Assembly.lean`
- `/tmp/mt-decomp/check/CubeCycle.lean`
- `/tmp/mt-decomp/check/CompMass.lean`

Pins match. The snapshot manifest records project b4d606db1 (= workspace HEAD) and mathlib 25730c7c; the snapshot Contract.lean equals the workspace Contract.lean and Submission.lean.

Library gaps. Simon leaves Lemma 7.3.5 to the reader (book/chapter-07.txt), so the supplied proof is the project's own argument. SimonGMT has:
- no general Cartesian products of currents;
- no slicing;
- no translation lemma for currents.
Snapshot mathlib has no currents at all ("Cartesian product of currents|slice of a current": no match).

Accepted reuse. dag.json has 2101 accepted declarations. Three fit this proof with byte-identical frozen types, present in their candidate commits:
- idtp_fons_cs_sos_product_current (4aa9ba8d): exactly the I.3 product construction; it also carries the AreaLipschitz import;
- lcmp_massOn_le_add_of_eval_eq (c7dea4b8): the mass triangle inequality;
- dimred_cs_ti_translate_action_hasDerivAt (f899c748): the derivative of s ↦ R.action(ω(sv + ·)).
These are reused as children. Inherited by exact-name citation (inherited.py): dtc_imrep_current, imrep_represents_massOn_eq_measure, imrep_carrier_sdiff_support_null, rsd_isIntegerMultiplicity_int_combination and dimred_im_mass_measure.

Mathlib facts the child proofs need are present in the snapshot, among them:
- μHE[k] = volume on EuclideanSpace and the isometry push-forward Isometry.map_euclideanHausdorffMeasure;
- PiLp.volume_preserving_toLp, Real.volume_pi_closedBall / volume_pi_ball and measurePreserving_piFinSuccAbove;
- the FTC integral_eq_sub_of_hasDerivAt, continuousAt_of_dominated and setIntegral_sdiff;
- finrank_span_eq_card and Submodule.eq_of_le_of_finrank_eq;
- SimonGMT exteriorDerivative_apply, GeometricCurrentOn.boundary_apply and the CountablyRectifiable / HasApproximateTangentSpaceAt definitions via blowUpMap images.

Lean checks. All 12 child types elaborate. The parent's frozen type compiles from the child stubs and its own dependency stubs (axioms: propext, sorryAx from stubs only, Classical.choice, Quot.sound). Skeletons of cube_cycle and competitor_mass compile against their sibling stubs. The runtime gates (ScopedDecomposition validation, _dependency_problem, _existing_lean_name_problem) pass on dag.json. The parallel node idtp_fons_cs_sos_minimality_transfer has the identical frozen type but is not accepted, so it is not reused.
