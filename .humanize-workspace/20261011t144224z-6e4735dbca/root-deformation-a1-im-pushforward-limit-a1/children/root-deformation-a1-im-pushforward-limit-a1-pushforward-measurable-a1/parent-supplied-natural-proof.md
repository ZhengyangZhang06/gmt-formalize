# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.im_pushforward_limit-a1`
- Child DAG node: `root.deformation-a1.im_pushforward_limit-a1.pushforward_measurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the measurability assertion of step (c) of the parent proof (“F is H^k⌞M-measurable: on each chart piece G_i of (e), F∘Φ_i is given by the formula of (f) … in terms of θ∘Φ_i, the measurable coefficient c and the minors of Du (Du is Borel, as an a.e. limit of difference quotients), and Φ_i⁻¹ maps H^k-null sets to L^k-null sets”), proved for the k-vector field x ↦ L(x)_#ξ(x) itself — the parent's F is θ(x) times its value at ω(g(x)) — for an arbitrary open U, locally Lipschitz f and arbitrary L with the derivative property. As in the parent the argument is chart by chart. Its chart ingredients are the siblings c1_cover (the C¹ charts of step (e)), chart_chain_rule (the tangent identification and chain rule of step (f)) and measurable_chart_differential (a Borel map reproducing the chart derivatives D(f∘Φ_j) through continuous left inverses of DΦ_j; this is the parent's “Du is Borel” plus the inverse chart).

Conventions. H := μHE[k] on ℝ^P and L^k := volume on ℝ^k, which equals μHE[k] on ℝ^k (InnerProductSpace.euclideanHausdorffMeasure_eq_volume with finrank ℝ^k = k). DΦ(w) := fderiv ℝ Φ w. For a linear A : ℝ^P → ℝ^Q, A_# := nVectorPushforward k A = (w ↦ w ∘ covectorPullback k A); it satisfies A_#(simpleNVector v) = simpleNVector(A∘v) (SimonGMT nVectorPushforward_simple) and A_#(−w) = −A_#w. A map Φ is c-antilipschitz on Ω if c|w − w′| ≤ |Φ(w) − Φ(w′)| for all w, w′ ∈ Ω. Put V(x) := L(x)_#ξ(x).

1. (Charts.) M is countably k-rectifiable (field countablyRectifiable of the triple). By the sibling c1_cover there are C¹ maps Φ_j : ℝ^k → ℝ^P and open sets Ω_j ⊆ ℝ^k (j ∈ ℕ) such that Φ_j is K_j-Lipschitz and c_j-antilipschitz on Ω_j for some K_j ≥ 0, c_j > 0, and H(M ∖ ⋃_jΦ_j(Ω_j)) = 0.

2. (A Borel comparison map.) By the sibling measurable_chart_differential, applied to the family (Φ_j, Ω_j)_j of step 1 and to f, there is a strongly measurable L̂ : ℝ^P → L(ℝ^P, ℝ^Q) such that every x ∈ ⋃_jΦ_j(Ω_j) admits j ∈ ℕ and w ∈ Ω_j with Φ_j(w) = x and L̂(x)(DΦ_j(w)s) = D(f∘Φ_j)(w)s for every s ∈ ℝ^k.

3. (Good parameters.) Fix j and put S_j := Ω_j ∩ Φ_j⁻¹(M). By the sibling chart_chain_rule (hypotheses: U open, the triple, f locally Lipschitz on U, the derivative hypothesis on L, Ω_j open, Φ_j C¹ and antilipschitz on Ω_j), for L^k-a.e. w ∈ S_j: (i) range DΦ_j(w) is a weighted approximate tangent space of (M, θ) at Φ_j(w), and (ii) f∘Φ_j has Fréchet derivative L(Φ_j(w))∘DΦ_j(w) at w, hence D(f∘Φ_j)(w) = L(Φ_j(w))∘DΦ_j(w). Let B_j be the set of w ∈ ℝ^k at which (i) or (ii) fails, so (L^k⌞S_j)(B_j) = 0; let T_j be a measurable hull of B_j for L^k⌞S_j (Mathlib toMeasurable) and E_j := T_j ∩ S_j. Then E_j ⊆ Ω_j, L^k(E_j) = (L^k⌞S_j)(T_j) = (L^k⌞S_j)(B_j) = 0, and (i), (ii) hold at every w ∈ S_j ∖ E_j.

4. (An H-null exceptional set.) Φ_j is K_j-Lipschitz on E_j ⊆ Ω_j, so H(Φ_j(E_j)) ≤ K_j^k·μHE[k](E_j) = K_j^k·L^k(E_j) = 0 (SimonGMT Chapter02 euclideanHausdorffMeasure_image_le_of_lipschitzOn). Let Z_or be the set of x ∈ M at which the orientation clause of the triple fails; it is H-null (field orients, M null-measurable). Hence N := (M ∖ ⋃_jΦ_j(Ω_j)) ∪ ⋃_jΦ_j(E_j) ∪ Z_or is H-null (countable subadditivity and step 1).

5. (Pointwise identity off N.) Let x ∈ M ∖ N. By the orientation clause, ξ(x) = ε·simpleNVector τ with ε ∈ {1, −1}, τ : Fin k → ℝ^P orthonormal and span τ a weighted approximate tangent space of (M, θ) at x. Since x ∈ ⋃_jΦ_j(Ω_j), step 2 provides j and w ∈ Ω_j with Φ_j(w) = x and L̂(x)∘DΦ_j(w) = D(f∘Φ_j)(w). Then w ∈ S_j (as Φ_j(w) = x ∈ M) and w ∉ E_j (otherwise x ∈ Φ_j(E_j) ⊆ N), so (i) and (ii) of step 3 hold at w. By (i), range DΦ_j(w) is a weighted approximate tangent space of (M, θ) at x; as θ(x) > 0 (field pos), weighted approximate tangent spaces at x are unique (SimonGMT HasWeightedApproximateTangentSpaceAt.unique), so span τ = range DΦ_j(w). Hence each τ_a equals DΦ_j(w)s_a for some s_a ∈ ℝ^k, and by step 2 and (ii), L̂(x)τ_a = D(f∘Φ_j)(w)s_a = L(x)(DΦ_j(w)s_a) = L(x)τ_a. Therefore L̂(x)∘τ = L(x)∘τ and
 V(x) = L(x)_#(ε·simpleNVector τ) = ε·simpleNVector(L(x)∘τ) = ε·simpleNVector(L̂(x)∘τ) = L̂(x)_#ξ(x).

6. (Conclusion.) The map (A, w) ↦ A_#w = w ∘ covectorPullback k A from L(ℝ^P, ℝ^Q) × NVector(ℝ^P, k) to NVector(ℝ^Q, k) is continuous: A ↦ covectorPullback k A is continuous (Mathlib ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM) and composition of continuous linear maps is jointly continuous. L̂ is strongly measurable and ξ is H⌞M-a.e. strongly measurable (field aestronglyMeasurable), so x ↦ L̂(x)_#ξ(x) is H⌞M-a.e. strongly measurable. By step 5 it agrees with V at every point of M ∖ N, i.e. H⌞M-a.e. (M is null-measurable and H(N) = 0). Hence V is H⌞M-a.e. strongly measurable. No case distinction is needed: for k = 0 (empty families; span of the empty family is {0}) and for k > P (then H = 0 on ℝ^P) the same argument applies verbatim. ∎

Lean evidence. Steps 1–6 were compiled against the frozen contract (toolchain v4.35.0-rc3, Mathlib 25730c7c), with the exact frozen types of the siblings c1_cover, chart_chain_rule and measurable_chart_differential as hypotheses; #print axioms reports only propext, Classical.choice and Quot.sound. Key library names: toMeasurable, Measure.restrict_apply, measure_iUnion_null, Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn, InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Eucl k) with finrank_euclideanSpace_fin, ae_restrict_iff'₀, measure_eq_zero_iff_ae_notMem, HasWeightedApproximateTangentSpaceAt.unique, HasFDerivAt.fderiv, nVectorPushforward_simple, ContinuousLinearMap.neg_comp, AEStronglyMeasurable.congr.

## Key steps

1. Sibling c1_cover: C¹ charts Φ_j, Lipschitz and antilipschitz on open Ω_j, cover M up to an H^k-null set.
2. Sibling measurable_chart_differential: a strongly measurable L̂ with L̂(x)∘DΦ_j(w) = D(f∘Φ_j)(w) at a chart preimage w of every covered point x.
3. Sibling chart_chain_rule: outside an L^k-null E_j ⊆ Ω_j, range DΦ_j(w) is a weighted tangent space at Φ_j(w) and D(f∘Φ_j)(w) = L(Φ_j(w))∘DΦ_j(w); Φ_j(E_j) is H^k-null by the Lipschitz image bound.
4. Off an H^k-null set: ξ(x) = ±simpleNVector τ, uniqueness of weighted tangent spaces gives span τ = range DΦ_j(w), hence L̂(x)τ_a = L(x)τ_a and L(x)_#ξ(x) = L̂(x)_#ξ(x).
5. (A, w) ↦ A_#w is continuous, so x ↦ L̂(x)_#ξ(x) is H^k⌞M-a.e. strongly measurable, and therefore so is x ↦ L(x)_#ξ(x).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (both byte-identical)`
- `python3 -I over dag.json: node root.deformation-a1.im_pushforward_limit-a1 has status decomposing, 'subproblem decomposition attempt 3', children [] (attempts 1-2 accepted by review but never activated)`
- `python3 -I over dag.json: status/candidate_commit/lean_statement of ltg_tau_unique_on_open, lpf_rectifiable_support_null, br_weightedTangent_congr, lpf_simple_nvector_algebra, cmb_covector_eq_sum_coord_smul_wedge, lpf_countably_rectifiable_c1_cover, lpf_chart_chain_rule, lpf_raf_chart_change_of_variables, lpf_tde_measurable_chart_differential (all accepted with candidate commits; types byte-identical to their handoffs and, for tau_unique/support_null, to the v2 children)`
- `python3 -I over dag.json: lean_name collisions for deformation_ipl_minor_weak_continuity, deformation_ipl_tangential_pushforward_aestronglyMeasurable, deformation_ipl_chart_convergence (none)`
- `rg -l 'deformation_ipl_' snapshot project, snapshot mathlib/Mathlib, lake-packages-25730c7c/simongmt/Poincare, GMT (no match)`
- `rg -n 'theorem HasWeightedApproximateTangentSpaceAt.unique|def nVectorPushforward|theorem nVectorPushforward_simple|def simpleNVector|theorem wedgeCovectors_apply_det|def covectorPullback' simongmt/Poincare/SimonGMT`
- `sed -n '205,260p' simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean (euclideanHausdorffMeasure_image_le_of_lipschitzOn)`
- `rg -n 'lemma locallyLipschitzOn_univ|LipschitzWith.locallyLipschitz|theorem IntegrableOn.mono_set_ae|theorem ae_le_set |theorem continuous_compContinuousLinearMapCLM|lemma tendsto_tsum_of_dominated_convergence|theorem integral_iUnion_ae|euclideanHausdorffMeasure_eq_volume|theorem measurable_fderiv |aestronglyMeasurable_iUnion_iff|LipschitzOnWith.extend_real|ae_convolution_tendsto_right_of_locallyIntegrable' snapshot mathlib/Mathlib`
- `git show a2a69a08f815abcf63c2e24fa1b57c6c02fdd1eb:GMT/Ch06/Submission.lean (accepted lpf_pi_measurability: continuity of (A, w) ↦ A_#w via ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM)`
- `python3 -I /tmp/ipl3/gen_types.py: verifier/lean_contract.py validate_lean_statement and gmt-compare.py contract_scope/child_modules for the twelve types`
- `lake env lean /tmp/ipl3/build/AllTypes.lean (exit 0, twelve sorry warnings); lake env lean /tmp/ipl3/build/Assembly.lean (exit 0, axioms propext, Classical.choice, Quot.sound); lake env lean /tmp/ipl3/build/ProtoPM.lean (exit 0, same axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-unique-on-open-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-support-null-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-ch-1ba1e0b708/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Tannery.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/ipl3/build/AllTypes.lean`
- `/tmp/ipl3/build/Assembly.lean`
- `/tmp/ipl3/build/ProtoPM.lean`

Pinned revisions are confirmed, and the frozen contract is byte-identical to the snapshot (Submission = Contract).
Reuse:
- The nine reused declarations are comparator-accepted with candidate commits.
- Their titles, statements and Lean types are copied byte-for-byte from dag.json.
- ltg_tau_unique_on_open and lpf_rectifiable_support_null are byte-identical to the v2 children tau_unique and support_null, which were then unaccepted.
New names: the three new names collide with nothing in dag.json, the project, SimonGMT or the pinned Mathlib.
Library support (all present in the snapshot, the SimonGMT names in the pinned package):
- SimonGMT: HasWeightedApproximateTangentSpaceAt.unique (needs θ x ≠ 0), nVectorPushforward_simple, wedgeCovectors_apply_det, euclideanHausdorffMeasure_image_le_of_lipschitzOn.
- Mathlib: integral_iUnion_ae, tendsto_tsum_of_dominated_convergence, measurable_fderiv, aestronglyMeasurable_iUnion_iff, continuous_compContinuousLinearMapCLM, LipschitzOnWith.extend_real, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable.
- No general weak-continuity-of-minors theorem exists in Mathlib or SimonGMT, and no accepted DAG node provides one (slicing_im_ll_gradient_weak_star, the first-order case, is still decomposing). minor_weak_continuity therefore stays a new child.
Lean checks:
- All twelve statements validate and elaborate in the exact comparator scope.
- The parent assembly compiles from four child types with only propext, Classical.choice and Quot.sound.
- The new measurability child compiles from its three sibling types with the same axioms.
