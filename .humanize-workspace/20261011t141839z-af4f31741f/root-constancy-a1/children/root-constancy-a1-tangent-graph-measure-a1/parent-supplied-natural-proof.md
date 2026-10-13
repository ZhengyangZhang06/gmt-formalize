# Parent-supplied natural-language proof

- Parent DAG node: `root.constancy-a1`
- Child DAG node: `root.constancy-a1.tangent_graph_measure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 8, Theorem 4.1 and its printed proof (pp. 213–214): displays (1)–(5) and the final paragraph.
Erratum (GMT/Ch08/README.md; SimonGMT ConstancyDomainCounterexample.counterexample_constancy_printed_hypotheses): the printed hypothesis "M connected" is replaced by "M ∩ U (pre)connected", and V = θ₀ v(M) is read in U. Counterexample to the printed version: U = ℝ∖{0}, M = ℝ, V = v((0,∞)) is stationary in U with spt ⊆ M, but it is not a constant multiple of v(M ∩ U). Connectedness of M ∩ U is exactly what the last line of the printed proof uses.
This child is the measure form "V = θ₀ v(M ∩ U)" of the theorem, i.e. steps 2–5 and 7 of the parent proof of root.constancy-a1. The sibling classical_tangent (Simon Ch. 2, 4.3) converts chart tangent planes into classicalTangentSpace.
Notation: μ := μ_V = V.weight; G := G(N,n) = Grassmannian N n; H^n := μHE[n]; p_S is orthogonal projection onto S; spt is support.

Hypotheses. V ∈ Varifold N n U with U open, and V is stationary in U (δV(X) = 0 for all X ∈ K(U;ℝ^N)). M is an n-dimensional C² submanifold in Simon's sense (IsSimonSubmanifold 2 M). U ∩ spt μ ⊆ M. M ∩ U is preconnected. M ≠ ∅.
Claim. There are c ∈ [0,∞] with c ≠ ∞ and a Borel T : ℝ^N → G such that V = (c · H^n⌞(M ∩ U)).map(x ↦ (x, T(x))). Moreover, if c ≠ 0, then ((T(x)).plane : Set ℝ^N) = classicalTangentSpace M x for every x ∈ M ∩ U.

1. Printed (1)–(2). Let f ∈ C²_c(U) vanish on M ∩ U. Then X := f∇f ∈ K(U;ℝ^N), and by 2.3
 div_S(f∇f) = ∇^S f·∇f + f div_S ∇f = |p_S(∇f)|² + f div_S ∇f.
 V is carried by G_n(U ∩ spt μ), and U ∩ spt μ ⊆ M ∩ U, where f = 0. Hence δV(f∇f) = ∫|p_S(∇f(x))|² dV(x,S) (printed (1)). Since δV = 0 and (x,S) ↦ |p_S(∇f(x))|² is continuous and ≥ 0, p_S(∇f(x)) = 0 for every (x,S) ∈ spt V with x ∈ U (printed (2)).
 [SimonGMT Varifold.Stationary.project_gradient_eq_zero_of_vanishing, ConstancySupport.lean:139.]

2. Printed (3). Let (x,S) ∈ spt V with x ∈ U.
 2a. x ∈ U ∩ spt μ ⊆ M, so by IsSimonSubmanifold x ∈ W ∩ M = φ(D) for a Simon C² representation φ : D → W ∩ M; write x = φ(a) with a ∈ D.
 2b. By the inverse function theorem and relative properness (Simon Ch. 2, 4.2) there are an open A ∋ x and F : ℝ^N → ℝ^N, C² on A, with F = 0 on M ∩ A and ker DF(x) = range Dφ(a). Here F = id − φ∘ψ, with ψ a C² local left inverse of φ [SimonGMT exists_local_normal_defining_map, ConstancyNormalCharts.lean:90].
 2c. Take a cutoff ζ ∈ C^∞_c(A ∩ U) with ζ = 1 near x, and let f_j := ζ·F_j for j = 1,…,N. Then f_j ∈ C²_c(U), and f_j = 0 on M ∩ U: on M ∩ A because F = 0 there, elsewhere because ζ = 0. Also ∇f_j(x) = ∇F_j(x) because F(x) = 0. So the ∇f_j(x) span the row space (ker DF(x))^⊥ = (range Dφ(a))^⊥.
 2d. Step 1 gives p_S(v) = 0 for all v ∈ (range Dφ(a))^⊥, i.e. (range Dφ(a))^⊥ ⊆ S^⊥, so S ⊆ range Dφ(a). Both are n-dimensional (Dφ(a) is injective), hence S = range Dφ(a) (printed (3)).
 [SimonGMT Stationary.plane_le_ker_fderiv_of_local_level_set; Stationary.plane_eq_parametrizedTangent, ConstancyNormalCharts.lean:188.]
 2e. In particular, for x ∈ U the fibre {S : (x,S) ∈ spt V} has at most one element, and range Dφ(a) does not depend on the chart (parametrizedTangent_eq_of_overlap).

3. Printed (4).
 3a. G is compact, so spt μ = π(spt V), where π(x,S) = x. Hence for x ∈ U ∩ spt μ the fibre is exactly one plane T(x), and x ↦ T(x) is continuous on U ∩ spt μ (closed graph into the compact G).
 3b. Since M ≠ ∅, a chart gives an n-plane P₀ = range Dφ(a₀) ∈ G. Setting T := P₀ off U ∩ spt μ gives a Borel map T : ℝ^N → G (U ∩ spt μ is Borel).
 3c. V is concentrated on spt V ∩ (U × G), which lies in the graph {(x, T(x)) : x ∈ U ∩ spt μ}. Hence V = μ.map(x ↦ (x, T(x))), i.e. ∫ f(x,S) dV(x,S) = ∫ f(x, T(x)) dμ(x) (printed (4)).
 [SimonGMT Stationary.exists_measurable_tangentGraph, ConstancyTangentGraph.lean:120.]

4. Printed (5).
 4a. V is stationary in every open ball contained in U, so by monotonicity (Ch. 8, 3.3/3.4) θ(x) := Θ^n(μ, x) exists and is finite at every x ∈ U.
 4b. On a chart sheet M ∩ W, λ := H^n⌞(M ∩ W) is locally finite (area formula), and Θ^n(λ, x) = 1 for every x ∈ M ∩ W (smooth chart).
 4c. μ⌞(W ∩ U) ≪ λ. Let Z ⊆ M ∩ W ∩ U with H^n(Z) = 0, and write Z = ∪_k Z_k with Z_k := {x ∈ Z : θ(x) ≤ k}. For δ, η > 0 put Z_{k,δ} := {x ∈ Z_k : μ(B_ρ(x)) ≤ (k+η)ω_nρ^n for 0 < ρ ≤ δ}, so Z_k = ∪_δ Z_{k,δ}. If Z_{k,δ} ⊆ ∪ C_i with diam C_i = d_i < δ and x_i ∈ C_i ∩ Z_{k,δ}, then Z_{k,δ} ⊆ ∪ B_{d_i}(x_i), so μ(Z_{k,δ}) ≤ (k+η)Σω_n d_i^n = 2^n(k+η)Σω_n(d_i/2)^n. Hence μ(Z_{k,δ}) ≤ 2^n(k+η)H^n_δ(Z) = 0, and μ(Z) = 0.
 4d. μ is carried by M ∩ U, because μ(ℝ^N∖U) = 0, μ(ℝ^N∖spt μ) = 0 and U ∩ spt μ ⊆ M.
 4e. Cover M ∩ U by countably many chart sheets (Lindelöf). Then μ ≪ H^n⌞M and μ is concentrated on M ∩ U. H^n⌞M is σ-finite (countably many compact chart pieces), so by Radon–Nikodym μ = θ̂ H^n⌞(M ∩ U) with θ̂ := dμ/d(H^n⌞M). θ̂ is ≥ 0, Borel, and locally H^n-integrable on U, since μ is finite on compact subsets of U.
 4f. The differentiation theorem (Ch. 1, 3.23) identifies θ̂ = θ H^n-a.e. on M ∩ U (printed (5)). Only the representation μ = θ̂ H^n⌞(M ∩ U) is used below.
 [SimonGMT Stationary.constancyDensity_representation, ConstancyHausdorffDensity.lean:124; constancyDensity is this Radon–Nikodym derivative.]

5. Printed final paragraph (corrected).
 5a. Fix x₀ = φ(a₀) ∈ M ∩ U with a Simon chart φ, a₀ ∈ D. There is an open ball B ∋ a₀ with B ⊆ D ∩ φ⁻¹(U) such that, for every ζ ∈ C¹_c(B) and v ∈ ℝ^n, some X ∈ K(U;ℝ^N) has spt X ⊆ W and X(φ(u)) = (ζ(u)/Jφ(u)) Dφ(u)v for u ∈ D. Here Jφ := (det DφᵀDφ)^{1/2} > 0 is C¹.
 Construction: take a C² local left inverse ψ of φ on a neighbourhood of φ(B̄) (inverse function theorem + 4.2) and a cutoff, and set X(y) := cutoff(y)·(ζ/Jφ)(ψ(y)) Dφ(ψ(y))v [SimonGMT exists_supported_tangent_coordinate_tests, ConstancyTangentTests.lean:74].
 5b. In local coordinates, div_M X(φ(u)) = Jφ(u)⁻¹ Σ_i ∂_i(Jφ Y_i)(u) with Y := (ζ/Jφ)v, i.e. div_M X ∘ φ = Jφ⁻¹ D_vζ [SimonGMT chartTangentialDivergence_coordinate_test, ConstancyPiola.lean:167].
 5c. By steps 3 and 4, 2.3, and the area formula ∫_{φ(K)} g dH^n = ∫_K g∘φ Jφ dL^n,
 0 = δV(X) = ∫_{M∩U} div_M X θ̂ dH^n = ∫_B D_vζ (θ̂∘φ) dL^n
 for every ζ ∈ C¹_c(B) and v ∈ ℝ^n. This is the printed display ∫ ∂ζ/∂x_i θ̃ dL^n = 0.
 5d. So θ̃ := θ̂∘φ, which is locally L^n-integrable on B, has zero distributional gradient on B. By mollification, θ̃ is L^n-a.e. constant on every ball contained in B [SimonGMT Stationary.exists_chart_density_weakDerivativesZero, WeakDerivativesZero.ae_eq_const_on_ball].
 5e. φ(B') is relatively open in M for every open B' ⊆ D (4.2), and φ maps L^n-null sets to H^n-null sets. Hence every point of M ∩ U has a relatively open neighbourhood in M ∩ U on which θ̂ is H^n-a.e. constant.
 5f. For c' ∈ [0,∞) let O_{c'} := {x ∈ M ∩ U : θ̂ = c' H^n-a.e. on some relatively open neighbourhood of x in M ∩ U}. The sets O_{c'} are relatively open and cover M ∩ U. They are pairwise disjoint because H^n charges every nonempty relatively open subset of M ∩ U: a chart image of a nonempty open set has positive H^n-measure by the area formula, since Jφ > 0.
 5g. M ∩ U is preconnected (CORRECTED hypothesis), so at most one O_{c'} is nonempty. Covering M ∩ U by countably many of the neighbourhoods (Lindelöf) gives θ̂ = θ₀ H^n-a.e. on M ∩ U for a constant θ₀ ∈ [0,∞); any θ₀ works if M ∩ U = ∅. Therefore μ = c·H^n⌞(M ∩ U) with c := θ₀ ∈ [0,∞), c ≠ ∞.
 [SimonGMT Stationary.density_ae_eq_const_of_connected_domain_carrier, ConstancyManifoldGluing.lean:224; Stationary.exists_const_simonHausdorff_connectedCarrier, ConstancyCorrected.lean:55.]

6. Measure identity. From steps 3 and 5, V = μ.map(x ↦ (x, T(x))) = (c·H^n⌞(M ∩ U)).map(x ↦ (x, T(x))), with T Borel and c ≠ ∞.

7. Tangent clause. Assume c ≠ 0 and let x ∈ M ∩ U.
 7a. Since x ∈ M, IsSimonSubmanifold gives D, W, φ with x ∈ W and Chapter02.IsSimonLocalRepresentation 2 M D W φ. Then x ∈ W ∩ M = φ(D), so x = φ(a) with a ∈ D.
 7b. Every neighbourhood O of x has H^n(O ∩ M ∩ U) > 0: D ∩ φ⁻¹(O ∩ U) is a nonempty open subset of D, and its image lies in O ∩ M ∩ U and has positive H^n-measure. So x ∈ spt(c·H^n⌞(M ∩ U)) = spt μ [SimonGMT mem_support_simonHausdorff_restrict_manifold and mem_weight_support_of_const_simonHausdorff, ConstancyCorrected.lean:30 and :87].
 7c. Hence x ∈ U ∩ spt μ, (x, T(x)) ∈ spt V by step 3, and (T(x)).plane = range Dφ(a) by step 2.
 7d. By the sibling lemma classical_tangent (Submission.simon_chart_classicalTangentSpace_eq_range applied to φ and a ∈ D), range Dφ(a) = Set.range (fderiv ℝ φ a) = classicalTangentSpace M (φ(a)) = classicalTangentSpace M x. So ((T(x)).plane : Set ℝ^N) = classicalTangentSpace M x. ∎

8. Formal route. This exact statement was proved in a scratch copy importing GMT.Ch08.Submission, Poincare.SimonGMT.Chapter08.ConstancyCorrected and Poincare.SimonGMT.Chapter02.AreaLiteral, with classical_tangent as the only sibling input and axioms propext, Classical.choice, Quot.sound only.
 8a. intro N n U V M hV hSM hM hconn hne.
 8b. obtain ⟨c, T, hc, hTm, -, -, hmeas, hchart⟩ := hV.exists_const_tangentGraph_connectedCarrier hSM hM hne hconn. This is Varifold.Stationary.exists_const_tangentGraph_connectedCarrier (Chapter08/ConstancyCorrected.lean:103), which packages steps 1–7 in chart form: c ≠ ⊤, Measurable T, V.measure = (c • (Chapter01.simonHausdorffMeasureReal (n:ℝ)).restrict (M ∩ U)).map (fun x ↦ (x, T x)), and (T (φ a)).plane = (fderiv ℝ φ a).range for every representation φ and a ∈ D with φ a ∈ U, when c ≠ 0.
 8c. rw [Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure] at hmeas (Chapter02/AreaLiteral.lean:42: simonHausdorffMeasureReal (n:ℝ) = μHE[n]).
 8d. refine ⟨c, T, hc, hTm, hmeas, ?_⟩; intro hc0 x hx.
 8e. obtain ⟨D, W, φ, hxW, hφ⟩ := hSM.exists_localRepresentation hx.1; obtain ⟨a, ha, rfl⟩ : x ∈ φ '' D := by rw [hφ.image_eq]; exact ⟨hxW, hx.1⟩.
 8f. rw [Submission.simon_chart_classicalTangentSpace_eq_range N n M W D φ a hφ ha, hchart hφ a ha hx.2 hc0]; exact LinearMap.coe_range _.

## Key steps

1. Printed (1)–(2): for f ∈ C²_c(U) vanishing on M ∩ U, δV(f∇f) = ∫|p_S∇f|² dV = 0, so p_S(∇f(x)) = 0 on spt V.
2. Printed (3): local defining maps F with ker DF(φ(a)) = range Dφ(a) give S = range Dφ(a) whenever (φ(a), S) ∈ spt V.
3. Printed (4): there is a unique support plane T(x) over U ∩ spt μ_V; extend it to a Borel T; then V = μ_V.map(x ↦ (x, T x)).
4. Printed (5): μ_V ≪ H^n⌞M and μ_V is carried by M ∩ U, so μ_V = θ H^n⌞(M ∩ U) with θ locally integrable.
5. Final paragraph (corrected): θ∘φ has zero weak gradient in charts, so θ is locally a.e. constant. Since M ∩ U is preconnected, θ = θ₀ a.e., so μ_V = c·H^n⌞(M ∩ U) with c = θ₀ < ∞.
6. Combine: V = (c·H^n⌞(M ∩ U)).map(x ↦ (x, T x)).
7. If c ≠ 0, then M ∩ U ⊆ spt μ_V, so plane(T(φ a)) = range Dφ(a) = classicalTangentSpace M (φ a) by classical_tangent.
8. Formal: SimonGMT Stationary.exists_const_tangentGraph_connectedCarrier + simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure + classical_tangent + LinearMap.coe_range.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum project/GMT/Ch08/Contract.lean and workspace GMT/Ch08/Submission.lean (both 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n classicalTangentSpace project/GMT/Ch08/Contract.lean (def :158, used in ConstancyTheorem :315)`
- `rg -n 'notation "μHE\[' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (:72)`
- `rg -n '^theorem coe_range' mathlib/Mathlib/Algebra/Module/Submodule/Range.lean (:60)`
- `rg -n 'theorem ContDiffOn.comp_contDiff|theorem HasFDerivAt.comp_hasDerivAt|theorem Ioo_mem_nhds' mathlib/Mathlib (ContDiff/Comp.lean:145, Deriv/Comp.lean:374, Topology/Order/OrderClosed.lean:611)`
- `rg -l -i 'classical ?tangent|tangent.*curve' mathlib/Mathlib/Geometry/Manifold (no match)`
- `grep -n '^theorem|^def' simongmt Chapter08/Constancy*.lean DistributionalConstancy.lean`
- `grep -rn -i 'curve|velocit' simongmt Chapter02/*.lean (only arc-length/area lemmas; no curve characterization of tangent spaces)`
- `grep -rln parametrizedTangentSpace simongmt (only Chapter02/Submanifold.lean, defined as range of fderiv)`
- `sed simongmt Chapter08/ConstancyCorrected.lean, ConstancyNormalCharts.lean, ConstancyTangent.lean, ConstancyTangentGraph.lean, ConstancySupport.lean, ConstancyTangentTests.lean, ConstancyChartWeakDerivatives.lean, ConstancyManifoldGluing.lean, ConstancyHausdorffDensity.lean; Chapter02/Submanifold.lean, SubmanifoldTopology.lean, AreaLiteral.lean`
- `grep -rl simon_chart_classicalTangentSpace_eq_range|stationary_constancy_tangentGraph_measure over run dir, simongmt, GMT (no collisions)`
- `sed verifier/gmt-compare.py child_modules/contract_scope/candidate_inputs; verifier/lean_contract.py validate_lean_statement`
- `lake build GMT.Ch08.Submission in /tmp scratch copy; lake env lean Scratch/ChallengeA.lean, Scratch/ChallengeB.lean (exact comparator challenge modules)`
- `lake env lean Scratch/Assembly.lean (full proofs of both children + ConstancyTheorem assembly + NodeSolution forms + #print axioms)`
- `python3 -I lean_contract.validate_lean_statement on both child statements (OK)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Algebra/Module/Submodule/Range.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Manifold`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyCorrected.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyNormalCharts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyTangent.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyTangentGraph.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancySupport.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyTangentTests.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyChartWeakDerivatives.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyManifoldGluing.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyHausdorffDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/tmp/constancy-a1-scratch/Scratch/Assembly.lean`
- `/tmp/constancy-a1-scratch/Scratch/ChallengeA.lean`
- `/tmp/constancy-a1-scratch/Scratch/ChallengeB.lean`

Snapshot = project 63436ae6 + Mathlib 25730c7c; its Contract.lean is byte-identical to the workspace Submission. Mathlib has no varifold theory and no curve-velocity characterization of tangent spaces of parametrized submanifolds (no match under Geometry/Manifold); pinned SimonGMT has none either (Chapter02 only defines parametrizedTangentSpace := range Dφ). So Simon Ch. 2, 4.3 (classical_tangent) is a genuine new obligation; it is proved from SimonGMT exists_local_normal_defining_map (ConstancyNormalCharts.lean:90) plus Mathlib calculus (ContDiffOn.comp_contDiff, HasFDerivAt.comp_hasDerivAt, Real.hasDerivAt_sin, Ioo_mem_nhds). The varifold content is the kernel-checked SimonGMT Varifold.Stationary.exists_const_tangentGraph_connectedCarrier (ConstancyCorrected.lean:103), stated with simonHausdorffMeasureReal and chart tangents; it is translated to μHE[n] via Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure (AreaLiteral.lean:42) and to classicalTangentSpace via classical_tangent and LinearMap.coe_range (Range.lean:60). #print axioms for these SimonGMT lemmas shows only propext, Classical.choice, Quot.sound. In a /tmp copy importing GMT.Ch08.Submission with the comparator's replayed Contract scope, both child statements elaborate (NodeChallenge form), pass validate_lean_statement, are fully proved, and assemble to ConstancyTheorem with standard axioms only; the new names collide with nothing.
