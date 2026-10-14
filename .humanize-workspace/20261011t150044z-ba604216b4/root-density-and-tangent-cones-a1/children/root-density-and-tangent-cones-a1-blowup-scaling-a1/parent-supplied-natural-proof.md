# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_scaling-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, 2.23–2.24 (push-forward, chapter-06.txt lines 405–440) and 3.3–3.9 (push-forward of integer multiplicity currents, lines 770–862); the scaling identity (1) in the proof of Simon 7.3.1 (chapter-07.txt lines 329–331); invariance of minimality under dilations is used in the proof of 7.3.1 (line 333) and in step 4(iv) of the parent proof ("dilations preserve minimality").
0. Facts about η. η is an affine bijection of ℝ^P with inverse η⁻¹(z) = x + λz and |η(y) − η(y')| = λ⁻¹|y − y'|.
 (i) Hⁿ(η(E)) = λ^{−n}Hⁿ(E) for every E ⊆ ℝ^P (Hⁿ = μHE[n] is translation invariant and Hⁿ(cE) = cⁿHⁿ(E) for c > 0: Mathlib euclideanHausdorffMeasure_smul₀, euclideanHausdorffMeasure_homothety_image). Hence for Borel E and Borel g ≥ 0 (or g integrable on η(E)): ∫_{η(E)} g dHⁿ = λ^{−n}∫_E g∘η dHⁿ.
 (ii) The pullback is (η^#ω)(y)(v₁,…,vₙ) = ω(η(y))(λ⁻¹v₁,…,λ⁻¹vₙ) = λ^{−n}ω(η(y))(v₁,…,vₙ); so η^#ω = λ^{−n}(ω∘η), |η^#ω(y)| = λ^{−n}|ω(η(y))| for the Euclidean coefficient norm, and tsupport η^#ω = η⁻¹(tsupport ω). By the definition of blowUp (affine push-forward of the restriction of T, with η⁻¹(η(U)) = U), S(ω) = T(η^#ω) for ω ∈ 𝒟ⁿ(η(U)). Conversely every ω' ∈ 𝒟ⁿ(U) equals η^#ω for exactly one ω ∈ 𝒟ⁿ(η(U)), namely ω = λⁿ(ω'∘η⁻¹). The same statements hold for any current Y ∈ 𝒟_n(U) and its push-forward η_#Y(ω) := Y(η^#ω).
 (iii) If ζ(α) = ±α(τ) then ζ(λ^{−n}α) = λ^{−n}ζ(α) (linearity).
1. Mass scaling. Let Y ∈ 𝒟_n(U) and W ⊆ ℝ^P. The map ω ↦ ω∘η = λⁿη^#ω is a bijection from the admissible forms for η_#Y on η(W) (ω ∈ 𝒟ⁿ(η(U)), tsupport ω ⊆ η(W), |ω| ≤ 1) onto the admissible forms for Y on W (tsupport(ω∘η) = η⁻¹(tsupport ω) ⊆ η⁻¹(η(W)) = W and |ω(η(y))| ≤ 1), and η_#Y(ω) = Y(η^#ω) = λ^{−n}Y(ω∘η). Since ofReal(λ^{−n}t) = ofReal(λ^{−n})·ofReal(t) and multiplication by the finite constant ofReal(λ^{−n}) commutes with suprema in [0, ∞], M_{η(W)}(η_#Y) = ofReal(λ^{−n})·M_W(Y). With Y = T this is (1).
2. Representation. Let R = (M, θ, ξ) represent T and define R' := (M', θ', ξ') with M' := η(M), θ' := θ∘η⁻¹, ξ' := ξ∘η⁻¹.
 - M' is Borel (image of a Borel set under a homeomorphism of ℝ^P) and M' ⊆ η(U).
 - M' is countably n-rectifiable: if M ⊆ M₀ ∪ ⋃_j F_j(ℝⁿ) with Hⁿ(M₀) = 0 and F_j Lipschitz, then M' ⊆ η(M₀) ∪ ⋃_j (η∘F_j)(ℝⁿ), Hⁿ(η(M₀)) = 0 by 0(i), and each η∘F_j is Lipschitz.
 - θ' is measurable, ℕ-valued, and θ' ≥ 1 on M'.
 - For compact K ⊆ η(U), η⁻¹(K) is a compact subset of U and ∫_{M'∩K} θ' dHⁿ = λ^{−n}∫_{M∩η⁻¹(K)} θ dHⁿ < ∞ by 0(i).
 - ξ' is a.e. strongly measurable for Hⁿ⌞M' (composition with the homeomorphism η⁻¹, which carries Hⁿ⌞M'-null sets to Hⁿ⌞M-null sets by 0(i)).
 - Orientation: let y ∈ M be such that Q := T_yM exists and ξ(y) orients Q (Hⁿ-a.e. y ∈ M), and z := η(y). For r > 0 and w ∈ ℝ^P, η_{z,r}(η(w)) = (η(w) − η(y))/r = (w − y)/(λr) = η_{y,λr}(w), so η_{z,r}(M') = η_{y,λr}(M) and ∫_{η_{z,r}(M')} f dHⁿ = ∫_{η_{y,λr}(M)} f dHⁿ → ∫_Q f dHⁿ as r ↓ 0 for every f ∈ C_c(ℝ^P). Hence HasApproximateTangentSpaceAt n M' z Q, and ξ'(z) = ξ(y) orients Q. The exceptional set in M' is the η-image of an Hⁿ-null set, hence null.
 - Representation: for ω ∈ 𝒟ⁿ(η(U)), by 0(ii),(iii) and 0(i): S(ω) = T(η^#ω) = ∫_M θ(y)ξ(y)(λ^{−n}ω(η(y))) dHⁿ(y) = λ^{−n}∫_M (θ'·ξ'(ω))(η(y)) dHⁿ(y) = ∫_{M'} θ'(z)ξ'(z)(ω(z)) dHⁿ(z).
 - Measure: for Borel B, μ_{R'}(B) = ∫_{M'∩B} θ' dHⁿ = λ^{−n}∫_{M∩η⁻¹(B)} θ dHⁿ = ofReal(λ^{−n})·μ_R(η⁻¹(B)). This proves (2).
3. Minimality. Assume T is minimizing in A. By (2), S is integer multiplicity. Let W' be open with closure W' compact and ⊆ η(U), S' ∈ 𝒟_n(η(U)) integer multiplicity with ∂S' = ∂S (n ≥ 1), and spt(S' − S) a compact subset of η(A) ∩ W'.
 (a) Define S'' ∈ 𝒟_n(U) by S''(ω') := S'(λⁿ(ω'∘η⁻¹)), the push-forward of S' by the affine map η⁻¹. It is linear, and continuous because ω' ↦ λⁿ(ω'∘η⁻¹) maps convergent sequences in 𝒟ⁿ(U) to convergent sequences in 𝒟ⁿ(η(U)) (supports are mapped by the homeomorphism η, derivatives transform by the chain rule for the affine map). By 0(ii), S''(η^#ω) = S'(ω) for ω ∈ 𝒟ⁿ(η(U)), i.e. η_#S'' = S' (= blowUp S'' x λ); likewise T(ω') = S(λⁿ(ω'∘η⁻¹)), so S'' − T is the η⁻¹-push-forward of S' − S.
 (b) S'' is integer multiplicity: apply the construction of step 2 to S' and the similarity η⁻¹ (which is the dilation η_{−λ⁻¹x, λ⁻¹}; step 2 used only that η is a similarity with ratio λ⁻¹, so it applies verbatim with λ replaced by λ⁻¹ and x by −λ⁻¹x).
 (c) Boundary: exterior differentiation commutes with affine pullback (SimonGMT exteriorDerivative_affinePullbackForm), so ∂S'' is the η⁻¹-push-forward of ∂S' = ∂S, which is the η⁻¹-push-forward of η_#∂T (SimonGMT boundary_affinePushforward); since the two push-forwards are mutually inverse, ∂S'' = ∂T.
 (d) Support: a current vanishes on an open set W₀ ⊆ η(U) iff its η⁻¹-push-forward vanishes on η⁻¹(W₀) (supports of test forms correspond under 0(ii)), and η⁻¹ maps open sets with compact closure in η(U) onto open sets with compact closure in U. Hence spt(S'' − T) = η⁻¹(spt(S' − S)), a compact subset of η⁻¹(η(A) ∩ W') = A ∩ W, where W := η⁻¹(W') is open with closure W = η⁻¹(closure W') compact and ⊆ U.
 (e) Minimality of T gives M_W(T) ≤ M_W(S''). By step 1 applied to Y = T and to Y = S'' (η_#S'' = S'): M_{W'}(S) = ofReal(λ^{−n})M_W(T) ≤ ofReal(λ^{−n})M_W(S'') = M_{W'}(S'). Hence S is minimizing in η(A), proving (3).

## Key steps

1. Pullback by η multiplies n-forms by λ^{−n} and composes with η; admissible forms correspond bijectively, giving M_{η(W)}(η_#Y) = λ^{−n}M_W(Y).
2. Push the representation forward: carrier η(M), multiplicity θ∘η⁻¹, orientation ξ∘η⁻¹; Hⁿ scales by λ^{−n} and approximate tangent planes are dilation invariant.
3. Pull competitors back by η⁻¹, use minimality of T and mass scaling to get minimality of the blow-up in η(A).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp … GMT/Ch07/Submission.lean (identical; snapshot project b4d606d, mathlib 25730c7c)`
- `rg -n 'def GeometricCurrentOn.massOn|massAdmissibleOn|massOn_le_liminf|def GeometricCurrentOn.support|zeroRegion|restrictDomain|affinePushforward|boundary_affinePushforward|exteriorDerivative_affinePullbackForm|instance .*Zero' simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,AffineCurrentPushforward}.lean`
- `rg -n 'structure RectifiableVarifold|exp_normalizedBallMass_monotoneOn|upperSemicontinuousOn_stationaryDensity|tendsto_densityQuotient_real' simongmt/Poincare/SimonGMT/Chapter04/{Basic,MeanCurvature,Density}.lean`
- `rg -n 'def CountablyRectifiable|CountablyRectifiable.mono|countablyRectifiable_iUnion|def HasApproximateTangentSpaceAt|HasApproximateTangentSpaceAt.unique' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; rg -n 'Upper Density|upperDensity' simongmt/Poincare/SimonGMT/Chapter01`
- `rg -n 'euclideanHausdorffMeasure_zero|euclideanHausdorffMeasure_smul₀|homothety_image' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; rg -n 'hausdorffMeasure_zero_singleton' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean; rg -n 'theorem sdiff_subset|alias diff_subset' mathlib/Mathlib/Order/BooleanAlgebra/Set.lean`
- `rg -l 'dtc_' runs/20261011T150044Z-ba604216b4 (no match) and lean_name inventory of dag.json / node JSON files (no collision)`
- `contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') from verifier/gmt-compare.py; lean_contract.validate_lean_statement on all ten child types`
- `lake build GMT.Ch07.Submission (scratch copy /tmp/dtc-decomp-kWMgQM/proj); lake env lean Check/Exact.lean; lake env lean Check/AssemblyExact.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/BooleanAlgebra/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Density.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/dtc-decomp-kWMgQM/proj/Check/Exact.lean`
- `/tmp/dtc-decomp-kWMgQM/proj/Check/AssemblyExact.lean`
- `/tmp/dtc-decomp-kWMgQM/scripts/stmts.py`

The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean. The SimonGMT library supplies the frozen objects used by the children (GeometricCurrentOn, massOn with the Euclidean coefficient norm and massAdmissibleOn, support/zeroRegion, restrictDomain, affinePushforward with boundary_affinePushforward and exteriorDerivative_affinePullbackForm, the Zero instance, WeaklyConvergesOn.massOn_le_liminf) and reusable analytic results (Chapter04 bounded-mean-curvature monotonicity exp_normalizedBallMass_monotoneOn and upperSemicontinuousOn_stationaryDensity, but for the strengthened RectifiableVarifold, so a bridge from IMRep is needed; Chapter03 CountablyRectifiable.mono, countablyRectifiable_iUnion, HasApproximateTangentSpaceAt and its uniqueness; Chapter01 Upper Density Theorem 3.6). It does not contain Federer–Fleming compactness, slicing, the flat-norm theorem 7.2, push-forward by non-affine maps, or the representation/mass identity 6.3.2(3); these are cited from Simon or proved in the children. Mathlib facts used: μHE[0] = μH[0] with μH[0]{x} = 1 (counting measure), μHE[d] scaling under homotheties, Set.sdiff_subset (Set.diff_subset is deprecated, so the Lean types use sdiff_subset). All ten child types elaborate in the comparator scope, the conditional assembly from the exact strings proves DensityAndTangentCones with only propext, Classical.choice and Quot.sound, and no dtc_ name occurs elsewhere in the run.
