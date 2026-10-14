# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_scaling-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_scaling-a1.rep_pushforward-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 2; Simon Ch. 6, 3.3–3.9 (push-forward of an integer multiplicity current by a Lipschitz map, Lemma 3.9; chapter-06.txt lines 770–862), specialized to the similarity η, whose Jacobian is the constant λ^{−n}, so that the area formula reduces to the scaling of Hⁿ; Simon Ch. 3, Definitions 1.1 and 1.4 (chapter-03.txt lines 12–16, 77–86).
Conventions. ℝ^P = Euclid P. For x ∈ ℝ^P and λ > 0, η := η_{x,λ} = dilation x λ, η(y) = −λ⁻¹x + λ⁻¹y = λ⁻¹(y − x), and ι(z) := x + λz. For V ⊆ ℝ^P (any subset), 𝒟ⁿ(V) = TestFormOn V n is the set of C^∞ maps ω : ℝ^P → Λⁿ(ℝ^P) (n-covectors) with compact topological support tsupport ω ⊆ V; elements of 𝒟ⁿ(V) are determined by their underlying forms. η_#Y := η_{x,λ#}Y = blowUp Y x λ for Y ∈ 𝒟_n(U). Hⁿ = μHE[n] and c := ofReal(λ^{−n}) ∈ (0,∞). An IMRep R = (M, θ, ξ) in U consists of a Borel set M ⊆ U that is countably n-rectifiable, a measurable θ : ℝ^P → ℕ with θ > 0 on M and ∫_{M∩K} θ dHⁿ < ∞ for every compact K ⊆ U, and ξ : ℝ^P → Λₙ(ℝ^P), a.e. strongly measurable for Hⁿ⌞M, such that for Hⁿ⌞M-a.e. y there is a subspace Q with HasApproximateTangentSpaceAt n M y Q and IsUnitOrientationOf (ξ(y)) Q. R.action(ω) = ∫_M θ(y)·ξ(y)(ω(y)) dHⁿ(y); R represents T iff T(ω) = R.action(ω) for all ω ∈ 𝒟ⁿ(U); μ_R = (Hⁿ⌞M) with density θ (IMRep.measure).
1. η is an affine homeomorphism of ℝ^P with inverse ι: η is y ↦ λ⁻¹y (a homeomorphism, λ⁻¹ ≠ 0) followed by the translation z ↦ z − λ⁻¹x, η(ι(z)) = λ⁻¹(x + λz − x) = z and ι(η(y)) = x + λ·λ⁻¹(y − x) = y. Hence η is a measurable embedding (a Borel isomorphism of ℝ^P): η maps Borel sets onto Borel sets, η⁻¹(η(s)) = s and η(η⁻¹(t)) = t for all sets s, t.
2. Key identity: for every Borel s, Hⁿ⌞η(s) = c·η_#(Hⁿ⌞s). Proof: for a measurable embedding η, every measure ν and every set t, (η_#ν)⌞t = η_#(ν⌞η⁻¹(t)) (Mathlib MeasurableEmbedding.restrict_map). With ν = Hⁿ and t = η(s): η_#(Hⁿ⌞s) = (η_#Hⁿ)⌞η(s) = (ofReal(λⁿ)·Hⁿ)⌞η(s) = ofReal(λⁿ)·(Hⁿ⌞η(s)) by hausdorff_scaling (ii). Since c·ofReal(λⁿ) = ofReal(λ^{−n}λⁿ) = 1, multiplying by c gives the claim. Consequences, for Borel s:
 (A) for g : ℝ^P → [0,∞], ∫_{η(s)} g dHⁿ = c·∫_s g∘η dHⁿ (lintegral against a scalar multiple of a measure, and MeasurableEmbedding.lintegral_map, which needs no measurability of g);
 (B) for g : ℝ^P → ℝ, ∫_{η(s)} g dHⁿ = λ^{−n}·∫_s g∘η dHⁿ for the Bochner integral (integral_smul_measure with c.toReal = λ^{−n}, and MeasurableEmbedding.integral_map, which holds for every g, integrable or not);
 (C) if a property q satisfies q(η(y)) for Hⁿ⌞s-a.e. y, then q holds Hⁿ⌞η(s)-a.e. (MeasurableEmbedding.ae_map_iff; a ν-null set is (c·ν)-null);
 (D) if h∘η is a.e. strongly measurable for Hⁿ⌞s, then h is a.e. strongly measurable for Hⁿ⌞η(s) (MeasurableEmbedding.aestronglyMeasurable_map_iff and AEStronglyMeasurable.smul_measure).
3. Definition of R' and verification of the IMRep conditions in η(U). Let R = (M, θ, ξ) represent T and put M' := η(M), θ' := θ∘ι, ξ' := ξ∘ι; then θ'(η(y)) = θ(y) and ξ'(η(y)) = ξ(y).
 (a) M' is Borel by step 1, and M' ⊆ η(U) since M ⊆ U.
 (b) M' is countably n-rectifiable: choose M₀ with Hⁿ(M₀) = 0 and Lipschitz F_j : ℝⁿ → ℝ^P (j ∈ ℕ) with M ⊆ M₀ ∪ ⋃_j F_j(ℝⁿ) (Simon 3.1.1, SimonGMT CountablyRectifiable). Then Hⁿ(η(M₀)) = ofReal(λ^{−n})·0 = 0 by hausdorff_scaling (i); each η∘F_j is Lipschitz, since η is the linear map λ⁻¹·id (Lipschitz with constant ‖λ⁻¹·id‖) followed by a translation (an isometry); and M' ⊆ η(M₀) ∪ ⋃_j (η∘F_j)(ℝⁿ), because y ∈ M₀ gives η(y) ∈ η(M₀) and y = F_j(v) gives η(y) = (η∘F_j)(v).
 (c) θ' is measurable (θ is measurable and ι is continuous) and ℕ-valued; for z = η(y) ∈ M' with y ∈ M, θ'(z) = θ(y) > 0.
 (d) Local integrability: let K ⊆ η(U) be compact. Then M' ∩ K = η(M ∩ η⁻¹(K)) (f(s ∩ f⁻¹(t)) = f(s) ∩ t for every map f; Set.image_inter_preimage), and M ∩ η⁻¹(K) is Borel (K is closed). By 2(A), ∫_{M'∩K} θ' dHⁿ = c·∫_{M∩η⁻¹(K)} θ'∘η dHⁿ = c·∫_{M∩η⁻¹(K)} θ dHⁿ. The set η⁻¹(K) is compact (η is a homeomorphism) and η⁻¹(K) ⊆ η⁻¹(η(U)) = U, so the last integral is finite by the local integrability of R; as c < ∞ the product is finite.
 (e) ξ' is a.e. strongly measurable for Hⁿ⌞M' by 2(D), because ξ'∘η = ξ is a.e. strongly measurable for Hⁿ⌞M.
 (f) Orientation: let p(z) be the statement “∃Q, HasApproximateTangentSpaceAt n M' z Q ∧ IsUnitOrientationOf (ξ'(z)) Q”. For Hⁿ⌞M-a.e. y there is Q with HasApproximateTangentSpaceAt n M y Q and IsUnitOrientationOf (ξ(y)) Q; for such y the sibling tangent_invariance gives HasApproximateTangentSpaceAt n (η(M)) (η(y)) Q, and ξ'(η(y)) = ξ(y), so p(η(y)) holds. Hence p∘η holds Hⁿ⌞M-a.e., and by 2(C) p holds Hⁿ⌞M'-a.e.
 Therefore R' := (M', θ', ξ') is an IMRep in η(U).
4. R' represents η_#T. Let ω ∈ 𝒟ⁿ(η(U)). By testform_correspondence (a) choose ω' ∈ 𝒟ⁿ(U) with ω'(y) = ω(η(y)) for all y; by testform_correspondence (c) and since R represents T, η_#T(ω) = λ^{−n}T(ω') = λ^{−n}R.action(ω') = λ^{−n}∫_M θ(y)ξ(y)(ω(η(y))) dHⁿ(y). On the other hand, by 2(B) with s = M and g(z) := θ'(z)·ξ'(z)(ω(z)), R'.action(ω) = ∫_{η(M)} g dHⁿ = λ^{−n}∫_M g(η(y)) dHⁿ(y) = λ^{−n}∫_M θ(y)ξ(y)(ω(η(y))) dHⁿ(y). The two expressions agree, so R'.Represents(η_#T).
5. Measure identity. Let B be Borel; then η⁻¹(B) is Borel and
 μ_{R'}(B) = ∫_B θ' d(Hⁿ⌞M') (density formula on the measurable set B)
 = c·∫_B θ' d(η_#(Hⁿ⌞M)) (step 2)
 = c·∫_{η⁻¹(B)} θ'∘η d(Hⁿ⌞M) (MeasurableEmbedding.restrict_map and MeasurableEmbedding.lintegral_map)
 = c·∫_{η⁻¹(B)} θ d(Hⁿ⌞M) = c·μ_R(η⁻¹(B)),
 i.e. μ_{R'}(B) = ofReal(λ^{−n})·μ_R(η⁻¹(B)). No hypothesis on U or n was used. ∎
Formalization notes (this exact statement was proved in a scratch build from the three siblings' exact types): define R' by the structure literal {carrier := dilation x λ '' R.carrier, mult := fun z => R.mult (x + λ • z), orient := fun z => R.orient (x + λ • z), …}; the measurable embedding is Homeomorph.measurableEmbedding of (Homeomorph.smulOfNeZero λ⁻¹ _).trans (Homeomorph.addLeft (−(λ⁻¹ • x))), whose coercion is dilation x λ; prove the restriction identity hkey once (Measure.restrict_smul, the sibling's map identity, MeasurableEmbedding.restrict_map, preimage_image_eq, smul_smul); Lipschitz constant via ((isometry_add_left (−(λ⁻¹ • x))).lipschitzWith.comp (dilationCLM P λ).lipschitzWith).comp hK; local integrability via image_inter_preimage, lintegral_smul_measure, MeasurableEmbedding.lintegral_map, ENNReal.mul_ne_top; representation via integral_smul_measure, MeasurableEmbedding.integral_map, ENNReal.toReal_ofReal; measure via withDensity_apply, Measure.restrict_smul, lintegral_smul_measure, MeasurableEmbedding.restrict_map, MeasurableEmbedding.lintegral_map; orientation via Measure.ae_smul_measure and MeasurableEmbedding.ae_map_iff.

## Key steps

1. Hⁿ⌞η(s) = ofReal(λ^{−n})·η_#(Hⁿ⌞s) for Borel s (restrict_map for the measurable embedding η and hausdorff_scaling (ii)); hence change of variables for lintegrals, Bochner integrals, a.e. statements and a.e. strong measurability.
2. R' := (η(M), θ∘ι, ξ∘ι): Borel, contained in η(U), countably n-rectifiable (η(M₀) null, η∘F_j Lipschitz), positive integer multiplicity, locally integrable (η⁻¹(K) compact in U), measurable orientation, and orienting approximate tangent planes a.e. by tangent_invariance.
3. Represents: η_#T(ω) = λ^{−n}T(ω∘η) = λ^{−n}∫_M θ ξ(ω∘η) dHⁿ = ∫_{η(M)} θ' ξ'(ω) dHⁿ.
4. Measure: μ_{R'}(B) = ofReal(λ^{−n})∫_{η⁻¹(B)} θ d(Hⁿ⌞M) = ofReal(λ^{−n})μ_R(η⁻¹(B)).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean GMT/Ch07/Submission.lean (both identical; manifest project b4d606d, mathlib 25730c7c)`
- `rg -n 'theorem MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀|theorem Isometry.euclideanHausdorffMeasure_image' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'theorem restrict_map \(μ|theorem ae_map_iff \{p' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n 'MeasurableEmbedding.lintegral_map|MeasurableEmbedding.integral_map |MeasurableEmbedding.aestronglyMeasurable_map_iff' mathlib/Mathlib`
- `rg -n 'theorem map_smul_univ' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean; rg -n 'comp_homeomorph' mathlib/Mathlib/Topology/Algebra/Support.lean; rg -n 'theorem preimage_closure|theorem image_closure' mathlib/Mathlib/Topology/Homeomorph/Defs.lean`
- `grep -n '^def\|^theorem' simongmt/Poincare/SimonGMT/Chapter06/{AffineCurrentPushforward,Mass,CurrentLocalEquality,Currents,Forms}.lean simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (affinePullbackForm, affinePushforward_apply, boundary_affinePushforward, exteriorDerivative_affinePullbackForm, massOn, massAdmissibleOn, restrictDomain_apply, zeroRegion, support, CountablyRectifiable, HasApproximateTangentSpaceAt, blowUpMap)`
- `grep -rl -F <each proposed lean_name> runs/20261011T150044Z-ba604216b4 (no match) and lean_name inventory of dag.json and all node JSON files (no collision)`
- `contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') from verifier/gmt-compare.py; lean_contract.validate_lean_statement on all eight child types`
- `lake build GMT.Ch07.Submission; lake env lean Check/FinalExact.lean, Check/FinalAssembly.lean, Check/FinalLeaves.lean with #print axioms (scratch /tmp/bscale-decomp-6cU90O/proj)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Module.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Homeomorph/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/bscale-decomp-6cU90O/proj/Check/FinalExact.lean`
- `/tmp/bscale-decomp-6cU90O/proj/Check/FinalAssembly.lean`
- `/tmp/bscale-decomp-6cU90O/proj/Check/FinalLeaves.lean`

The snapshot contract and submission (project b4d606d, mathlib 25730c7c) are byte-identical to the workspace files. SimonGMT supplies the objects the children reason about: blowUp is an affinePushforward of a restrictDomain; affinePullbackForm comes with affinePushforward_apply, boundary_affinePushforward and exteriorDerivative_affinePullbackForm (used for blowup_structure (iv)); massOn/massAdmissibleOn (mass_scaling); zeroRegion/support/VanishesOn (blowup_structure (iii)); CountablyRectifiable and HasApproximateTangentSpaceAt via blowUpMap (rep_pushforward, tangent_invariance). It contains no dilation or blow-up lemmas, so the children supply them. The pinned Mathlib supplies the measure-theoretic and multilinear ingredients: euclideanHausdorffMeasure_smul₀ and Isometry.euclideanHausdorffMeasure_image (hausdorff_scaling); MeasurableEmbedding.restrict_map, lintegral_map, integral_map, ae_map_iff and aestronglyMeasurable_map_iff (rep_pushforward); ContinuousAlternatingMap.map_smul_univ and HasCompactSupport.comp_homeomorph (testform_correspondence); Homeomorph.preimage_closure and image_closure (blowup_structure, minimality). All eight child types elaborate in the comparator scope. Scratch Lean proofs of every child, and of the parent from the children, compile using only propext, Classical.choice and Quot.sound. No proposed name occurs elsewhere in the run.
