# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.flat_convergence-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.flat_convergence-a1.localize-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 (with step 2) of the parent proof, i.e. Simon Ch. 6, proof of Theorem 7.2, (4): "by 4.5(1),(2) and an argument as in 6.7(2) of Ch. 2 we can find a subsequence … such that sup_j M(∂(T_j⌞W_i)) < ∞", together with the weak convergence of the localized currents, which the parent proof obtains from the absence of limiting mass on the slicing level. Notation: for an IMRep R = (M, θ, ξ) in U, R.measure = θHⁿ⌞M; ‖ω‖_∞ := sup_x |ω(x)| < ∞ for a test form ω (continuous with compact support); M := M_U.
Facts about an IMRep R = (M, θ, ξ) in U representing a current Z ∈ 𝒟_d(U):
(R1) R.measure(K₁) = ∫_{M∩K₁} θ dH^d < ∞ for compact K₁ ⊆ U (field locallyIntegrable_mult).
(R2) Z(ω) = ∫⟨ω, ξ⟩ dR.measure for ω ∈ 𝒟^d(U): R.measure = (H^d⌞M).withDensity θ with θ measurable, so ∫ f dR.measure = ∫_M θ f dH^d (Mathlib integral_withDensity_eq_integral_smul for the ℝ≥0-valued θ), and Z(ω) = R.action(ω) = ∫_M θ⟨ω, ξ⟩ dH^d.
(R3) For R.measure-a.e. x, |⟨α, ξ(x)⟩| ≤ |α| for every d-covector α: (IO) gives this for H^d⌞M-a.e. x, and R.measure ≪ H^d⌞M (Mathlib withDensity_absolutelyContinuous). Consequently, for ω ∈ 𝒟^d(U) and Borel B with R.measure(B) < ∞, the function f(x) := ⟨ω(x), ξ(x)⟩ is R.measure-a.e. strongly measurable (R4; ω is continuous and evaluation is continuous) with |f| ≤ ‖ω‖_∞ R.measure-a.e., hence integrable on B (Mathlib Measure.integrableOn_of_bounded / IntegrableOn.of_bound), |∫_B f dR.measure| ≤ ‖ω‖_∞·R.measure(B).toReal, and if |ω| ≤ 1 everywhere then ∫_B f dR.measure ≤ R.measure(B).toReal; the same holds for χf with any measurable χ with values in [0, 1].
(R4) ξ is R.measure-a.e. strongly measurable (field aestronglyMeasurable_orient and absolute continuity, AEStronglyMeasurable.mono_ac).
(R5) M_V(Z) = R.measure(V) for open V (ME).
(R6) For Borel E, (IR) gives a current Z⌞E ∈ 𝒟_d(U) represented by an IMRep with carrier M ∩ E, multiplicity θ and orientation ξ; its measure is R.measure⌞E, because (H^d⌞(M ∩ E)).withDensity θ = ((H^d⌞M).withDensity θ)⌞E. By (R2), Z⌞E(ω) = ∫_E⟨ω, ξ⟩ dR.measure; in particular Z⌞E is IM.
0. (Case W = ∅.) Take φ := id, K := ∅, Λ := 0 and T'_j := T' := T⌞∅ (R6 with E := ∅). By (R6), T⌞∅(ω) = 0 for every ω, so T⌞∅ = 0: it is IM; its support is empty (each x ∈ U has a ball with compact closure in U, U being open, on which it vanishes); its mass and the mass of its boundary (the zero current) are 0; the constant sequence converges weakly; and a form with tsupport ⊆ ∅ is identically 0, so T'_j(ω) = 0 = T_j(ω) and T'(ω) = 0 = T(ω) by linearity. From now on W ≠ ∅.
1. (Geometry.) C := closure(W) is nonempty, compact and contained in U. By Mathlib IsCompact.exists_cthickening_subset_open there is δ₀ > 0 with cthickening(δ₀, C) ⊆ U; put δ := δ₀/3, so cthickening(3δ, C) ⊆ U. Let g(x) := infDist(x, C); g is 1-Lipschitz (Mathlib lipschitz_infDist_pt), continuous, and g = 0 on C ⊇ W. Since C ≠ ∅, infEDist(x, C) = ENNReal.ofReal(infDist(x, C)) (infEDist(x, C) ≠ ∞ for nonempty C, Mathlib Metric.infEDist_ne_top), so for 0 ≤ r the set {g ≤ r} equals cthickening(r, C) = {x : infEDist(x, C) ≤ ENNReal.ofReal(r)}; it is closed (g is continuous) and bounded (C is bounded), hence compact, and for r ≤ 3δ it is contained in cthickening(3δ, C) ⊆ U. W₁ := {g < 5δ/2} is open with closure(W₁) ⊆ {g ≤ 5δ/2}, compact and contained in U. By hypothesis Λ₀ := sup_j (M_{W₁}(T_j) + M_{W₁}(∂T_j)) < ∞.
2. (Representations.) For each j fix an IMRep R_j = (M_j, θ_j, ξ_j) of T_j. For every open V with closure(V) compact and contained in U, M_V(∂T_j) ≤ sup_i (M_V(T_i) + M_V(∂T_i)) < ∞, so ∂T_j is IM by (BR); fix an IMRep R'_j = (M'_j, θ'_j, ξ'_j) of ∂T_j. Fix an IMRep R_T of T. Put μ_j := R_j.measure, μ'_j := R'_j.measure and μ_T := R_T.measure.
3. (Slicing.) For each j apply (SL) with k := m, T := T_j, (μ, ξ) := (μ_j, ξ_j), (μ', ξ') := (μ'_j, ξ'_j), f := g and L := 1. Its hypotheses hold by (R1)–(R4) for R_j and for R'_j (which represents ∂T_j) and because g is 1-Lipschitz. It yields A_j(t) ∈ 𝒟_n(U), B_j(t) ∈ 𝒟_m(U) (t ∈ ℝ) with A_j(t)(ω) = ∫_{g<t}⟨ω, ξ_j⟩ dμ_j and B_j(t)(η) = ∫_{g<t}⟨η, ξ'_j⟩ dμ'_j, and, for Z_j(t) := ∂A_j(t) − B_j(t), every open V and every t: M_V(Z_j(t)) ≤ liminf_{h→0+} ENNReal.ofReal(h⁻¹)·μ_j(V ∩ {t − h < g < t}).
4. (Good level.) Let λ_j := μ_j.map g, a Borel measure on ℝ (g is continuous, hence measurable) with λ_j(E) = μ_j(g⁻¹(E)) for Borel E. Since {δ ≤ g ≤ 2δ} ⊆ W₁, λ_j([δ, 2δ]) ≤ μ_j(W₁) = M_{W₁}(T_j) ≤ Λ₀ (R5). The sibling good_slice with a := δ, b := 2δ and Λ := Λ₀ gives s ∈ (δ, 2δ), a strictly increasing φ and C₁ ∈ [0, ∞) such that (i) liminf_{h→0+} ENNReal.ofReal(h⁻¹)·μ_{φ(j)}({s − h < g < s}) ≤ C₁ for every j, and (ii) for every ε > 0 there is δ_ε > 0 with μ_{φ(j)}({s − δ_ε ≤ g ≤ s}) ≤ ε for all large j.
5. (Definitions.) G := {g < s} is open, W ⊆ C ⊆ G and G ⊆ W₁; K := {g ≤ s} is compact, K ⊆ U and G ⊆ K. Put T'_j := A_{φ(j)}(s), T' := T⌞G (R6 with E := G) and Λ := (Λ₀ + C₁).toNNReal, so that Λ = Λ₀ + C₁ in [0, ∞].
6. (IM.) T' is IM by (R6). By (R6) for R_{φ(j)} and E := G, T_{φ(j)}⌞G(ω) = ∫_G⟨ω, ξ_{φ(j)}⟩ dμ_{φ(j)} = T'_j(ω) for every ω, so T'_j = T_{φ(j)}⌞G is IM.
7. (Support.) Let x ∈ U ∖ K, so g(x) > s. The open set U ∩ {g > s} contains x; choose r > 0 with closedBall(x, r) ⊆ U ∩ {g > s}. V := ball(x, r) is open with compact closure contained in U, and V ∩ G = ∅. If ω ∈ 𝒟ⁿ(U) and tsupport ω ⊆ V, then ω = 0 on G and T'_j(ω) = ∫_G⟨ω, ξ_{φ(j)}⟩ dμ_{φ(j)} = 0. So V lies in the zero region of T'_j and x ∉ spt T'_j; as spt T'_j ⊆ U by definition, spt T'_j ⊆ K.
8. (Mass bounds.) (a) If ω is admissible for M_U (|ω| ≤ 1), then T'_j(ω) = ∫_G⟨ω, ξ_{φ(j)}⟩ dμ_{φ(j)} ≤ μ_{φ(j)}(G) by (R3); hence M(T'_j) ≤ μ_{φ(j)}(G) ≤ μ_{φ(j)}(W₁) = M_{W₁}(T_{φ(j)}) ≤ Λ₀ ≤ Λ (R5). (b) In the same way M(B_{φ(j)}(s)) ≤ μ'_{φ(j)}(G) ≤ μ'_{φ(j)}(W₁) = M_{W₁}(∂T_{φ(j)}) ≤ Λ₀ (R3 and R5 for R'_{φ(j)}). By step 3 with V := ℝ^P and by (i), M(Z_{φ(j)}(s)) = M_U(Z_{φ(j)}(s)) ≤ M_{ℝ^P}(Z_{φ(j)}(s)) ≤ liminf_{h→0+} ENNReal.ofReal(h⁻¹)·μ_{φ(j)}(ℝ^P ∩ {s − h < g < s}) ≤ C₁ (mass is monotone in the region). Since ∂T'_j(η) = B_{φ(j)}(s)(η) + Z_{φ(j)}(s)(η) for all η, for admissible η we get ENNReal.ofReal(∂T'_j(η)) ≤ ENNReal.ofReal(B_{φ(j)}(s)(η)) + ENNReal.ofReal(Z_{φ(j)}(s)(η)) ≤ M(B_{φ(j)}(s)) + M(Z_{φ(j)}(s)); hence M(∂T'_j) ≤ Λ₀ + C₁ = Λ.
9. (Agreement on W.) If tsupport ω ⊆ W ⊆ G, then ω = 0 outside G, so T'_j(ω) = ∫_G⟨ω, ξ_{φ(j)}⟩ dμ_{φ(j)} = ∫⟨ω, ξ_{φ(j)}⟩ dμ_{φ(j)} = T_{φ(j)}(ω) by (R2); likewise T'(ω) = ∫_G⟨ω, ξ_T⟩ dμ_T = T(ω).
10. (Weak convergence.) Fix ω ∈ 𝒟ⁿ(U), put c := ‖ω‖_∞ and let ε ∈ (0, ∞). The sets {s − 1/(i+1) < g < s} decrease to ∅ and μ_T(G) ≤ μ_T(K) < ∞ (R1), so by continuity from above there is δ₁ > 0 with μ_T({s − δ₁ < g < s}) ≤ ε. By (ii) there is δ₂ > 0 with μ_{φ(j)}({s − δ₂ ≤ g ≤ s}) ≤ ε for all large j. Let δ' := min(δ₁, δ₂, s/2) > 0. By Mathlib exists_contMDiffMap_one_nhds_of_subset_interior (closed set {g ≤ s − δ'}, t := {g ≤ s − δ'/2}, whose interior contains the open set {g < s − δ'/2} ⊇ {g ≤ s − δ'}) there is a smooth χ : ℝ^P → [0, 1] with χ = 1 on {g ≤ s − δ'} and χ = 0 outside {g ≤ s − δ'/2}; then tsupport χ ⊆ {g ≤ s − δ'/2}, which is compact and contained in G ⊆ U, so χω ∈ 𝒟ⁿ(U). By (R3) the functions ⟨ω, ξ_{φ(j)}⟩ and χ⟨ω, ξ_{φ(j)}⟩ are μ_{φ(j)}-integrable on G (bounded by c a.e., μ_{φ(j)}(G) ≤ μ_{φ(j)}(K) < ∞ by (R1)), and the same holds for μ_T, so the integrals below may be split linearly. Since χ = 0 outside G, (R2) gives T_{φ(j)}(χω) = ∫_G χ⟨ω, ξ_{φ(j)}⟩ dμ_{φ(j)}, hence T'_j(ω) − T_{φ(j)}(χω) = ∫_G (1 − χ)⟨ω, ξ_{φ(j)}⟩ dμ_{φ(j)}; the integrand vanishes on {g ≤ s − δ'} and has absolute value ≤ c for μ_{φ(j)}-a.e. x (R3). Thus |T'_j(ω) − T_{φ(j)}(χω)| ≤ c·μ_{φ(j)}({s − δ' < g < s}) ≤ c·μ_{φ(j)}({s − δ₂ ≤ g ≤ s}) ≤ cε for all large j, and likewise |T'(ω) − T(χω)| ≤ c·μ_T({s − δ' < g < s}) ≤ c·μ_T({s − δ₁ < g < s}) ≤ cε. Since T_{φ(j)}(χω) → T(χω) (T_j ⇀ T and φ(j) → ∞), limsup_j |T'_j(ω) − T'(ω)| ≤ 2cε. As ε > 0 was arbitrary, T'_j(ω) → T'(ω); hence T'_j ⇀ T' in U.
11. The data φ, K, Λ, (T'_j)_j and T' satisfy all requirements (steps 5–10). ∎

## Key steps

1. IMReps of T_j, of ∂T_j (IM by (BR)) and of T give measures with |ξ| ≤ 1 a.e. (IO) and M_V = measure on open V (ME), as required by (SL).
2. Slicing by g = dist(·, closure W) gives T_j⌞{g < t}, (∂T_j)⌞{g < t} and pointwise slice-mass bounds; the sibling good_slice picks s ∈ (δ, 2δ) and a subsequence with bounded slice masses and no limiting mass concentration at {g = s}.
3. T'_j := T_{φ(j)}⌞{g < s} and T' := T⌞{g < s} are IM (IR), supported in {g ≤ s}, have M(T'_j) ≤ Λ₀ and M(∂T'_j) ≤ Λ₀ + C₁, and agree with T_{φ(j)}, T on forms supported in W.
4. A cutoff χ = 1 on {g ≤ s − δ'} and the no-concentration bound give T'_j ⇀ T'.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean; mathlib/simongmt revs in lake-manifest.json`
- `python3 scans of RUN/dag.json: selected node and the frozen types of its six depends_on; nodes with lean_statement identical to the selected one (root.compactness_of_minimizing_currents-a1.flat_convergence-a1) and to each proposed child; statuses of that subtree; lean_name prefix dimred_mbl_fc (no match); node count 821`
- `read RUN/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1/decomposition-v1.json; git show a4486f3c7cd80fe7b0fa778632a5bc063d6a7748 (speculative assembly of cmc_flat_convergence)`
- `grep -n '_existing_lean_name_problem|depends_on|prerequisite_ids|existing_by_name' /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py; contract_scope/child_modules in verifier/gmt-compare.py`
- `#check after import GMT.Ch07.Submission: Poincare.SimonGMT.Chapter01.simon_theorem_4_16_compact_metrizable, MeasureTheory.FiniteMeasure, MonotoneOn.intervalIntegrable_deriv, MonotoneOn.intervalIntegral_deriv_mem_uIcc (unknown); Measure.countable_meas_level_set_pos, measurable_deriv, tendsto_of_subseq_tendsto, lintegral_liminf_le, Monotone.countable_not_continuousAt, IsCompact.tendsto_subseq, exists_contMDiffMap_one_nhds_of_subset_interior, IsCompact.exists_cthickening_subset_open, Finite.exists_infinite_fiber, extraction_of_frequently_atTop, measurable_measure_prodMk_left, lintegral_lintegral_swap, integral_withDensity_eq_integral_smul, withDensity_absolutelyContinuous, AEStronglyMeasurable.mono_ac, GeometricCurrentOn.boundary_boundary, WeaklyConvergesOn.boundary, WeaklyConvergesOn.massOn_le_liminf, countablyRectifiable_of_measure_zero (exist)`
- `lake env lean /tmp/fcB/FinalTypes.lean (8 child challenges) and /tmp/fcB/FinalAssembly.lean (#print axioms AssemblyCond); lean_contract.validate_lean_statement on all child types`
- `sed -n on SimonGMT Chapter06 Currents.lean (GeometricCurrentOn, TestFormOnConverges, WeaklyConvergesOn), Mass.lean (massAdmissibleOn, massOn, mass), CurrentLocalEquality.lean (restrictDomain, zeroRegion, support); book/chapter-06.txt lines 2000–2145 (7.1–7.2) and 290–305 (2.11)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-flat-convergence-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1/decomposition-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/fcB/FinalTypes.lean`
- `/tmp/fcB/FinalAssembly.lean`

The pins match: HEAD b4d606d, Mathlib 25730c7c, SimonGMT 2b366308. Submission.lean is byte-identical to the frozen contract.

Availability in the pinned libraries:
- SimonGMT supplies currents, sequential continuity, mass/massOn as sups over admissible forms, support, restrictDomain, weak convergence, ∂∂ = 0, boundary weak continuity and lower semicontinuity of mass.
- The pinned libraries lack flat convergence, the deformation theorem and slicing; these come from the parent's prerequisites.
- simon_theorem_4_16_compact_metrizable, FiniteMeasure and the MonotoneOn deriv-integral lemmas are outside the import closure. good_slice therefore uses Helly selection and Tonelli/Fatou instead.

The only accepted declaration with a child type is dtc_vanish_off_support, which is reused with its identical type. The parallel node cmc_flat_convergence has the identical parent type; its seven audited child types are reused verbatim under fresh dimred_mbl_fc_* names, since those nodes are unaccepted under another parent.

Results: all 8 child types elaborate, and the conditional assembly proves the exact parent type from the six prerequisite types and the child types (axioms propext, Classical.choice, Quot.sound).
