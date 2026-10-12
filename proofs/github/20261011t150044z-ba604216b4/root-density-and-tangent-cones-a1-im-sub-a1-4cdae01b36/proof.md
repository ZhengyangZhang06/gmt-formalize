# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.im_sub-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, Remark 3.2(1) (chapter-06.txt lines 755–756, stated without proof). Tools: the Upper Density Theorem, Ch. 1, 3.6 with Remark 3.7(2) (chapter-01.txt lines 700–722; SimonGMT Chapter01/DensityComparison.lean), and the fact that approximate tangent spaces only depend on a set up to sets of zero density, Ch. 3, 1.4–1.5 and Remark 1.8(1) (chapter-03.txt lines 77–108, 298–310). Throughout Hⁿ = μHE[n], η_{x,r}(y) := r⁻¹(y − x) (SimonGMT blowUpMap), and Hⁿ(η_{x,r}(E)) = r^{−n}Hⁿ(E) for all E (μHE[n] is translation invariant and n-homogeneous: Mathlib euclideanHausdorffMeasure_smul₀). Let R₁ = (M₁, θ₁, ξ₁) and R₂ = (M₂, θ₂, ξ₂) be IMReps in U representing S and T.
1. Local finiteness. For compact K ⊆ U, Hⁿ(M_i ∩ K) ≤ ∫_{M_i∩K} θ_i dHⁿ < ∞ since θ_i ≥ 1 on M_i. Hence every Borel A ⊆ M₁ ∪ M₂ has Hⁿ(A ∩ K) < ∞ for compact K ⊆ U.
2. (F1) If A ⊆ M₁ ∪ M₂ is Borel, then ρ^{−n}Hⁿ(A ∩ B_ρ(y)) → 0 as ρ ↓ 0 for Hⁿ-a.e. y ∈ U ∖ A. Proof: let V_j be open sets with compact closures in U and ⋃_j V_j = U; apply Ch. 1, 3.6 to the finite Borel-regular measure Hⁿ⌞(A ∩ V_j) to get the conclusion for Hⁿ-a.e. y ∈ V_j ∖ A (for y ∈ V_j and small ρ, B_ρ(y) ⊆ V_j), and take the union of the countably many exceptional null sets.
3. (F2) Let A, A' be Hⁿ-measurable, y ∈ U, s > 0 with Hⁿ(A ∩ B_s(y)), Hⁿ(A' ∩ B_s(y)) < ∞, ρ^{−n}Hⁿ((A Δ A') ∩ B_ρ(y)) → 0, and HasApproximateTangentSpaceAt n A y Q. Then HasApproximateTangentSpaceAt n A' y Q. Proof: finrank Q = n is unchanged. For f ∈ C_c(ℝ^P) with spt f ⊆ B_L(0) and 0 < r < s/L both blow-up integrals are finite and |∫_{η_{y,r}(A')} f dHⁿ − ∫_{η_{y,r}(A)} f dHⁿ| ≤ sup|f|·Hⁿ(η_{y,r}(A Δ A') ∩ B_L(0)) = sup|f|·r^{−n}Hⁿ((A Δ A') ∩ B_{Lr}(y)) → 0, so the blow-up integrals of A' converge to ∫_Q f dHⁿ as well.
4. (F3) If ζ and ζ' are both unit orientations of the same n-dimensional subspace Q (IsUnitOrientationOf), then ζ' = ±ζ: if ζ(α) = σα(τ) and ζ'(α) = σ'α(τ') with τ, τ' orthonormal bases of Q, then τ' = τB for an orthogonal n×n matrix B, and multilinearity plus the alternating property give α(τ') = det(B)α(τ) with det B = ±1.
5. Normalization. Changing ξ_i on an Hⁿ⌞M_i-null set changes neither the integrals in R_i.Represents nor the almost-everywhere statement `orients`; so we may assume ξ₁, ξ₂ Borel measurable. Put E := M₁ ∩ M₂. For increasing I : {1,…,n} → {1,…,P} let e^I ∈ Λⁿ(ℝ^P) be the covector e^I(v₁,…,vₙ) = det(⟨e_{I(a)}, v_b⟩)_{a,b}; these form a basis of Λⁿ(ℝ^P), so an n-vector ζ (a linear functional on Λⁿ) is determined by the numbers ζ(e^I). If ζ(α) = ±α(τ) for an orthonormal frame τ, then ζ ≠ 0 (the covector (v₁,…,vₙ) ↦ det(⟨τ_a, v_b⟩) takes the value ±1 under ζ), hence Σ_I ζ(e^I)² > 0.
6. Common tangent planes. For Hⁿ-a.e. y ∈ M_i the approximate tangent space T_yM_i exists and ξ_i(y) orients it. By F1 (with A = M₁ ∖ M₂ and A = M₂ ∖ M₁) and F2 (with A = M_i, A' = E, since M_i Δ E ⊆ M₁ ∖ M₂ or ⊆ M₂ ∖ M₁ and y ∉ these sets), for Hⁿ-a.e. y ∈ E the space T_yE exists and T_yM₁ = T_yE = T_yM₂. By F3, for Hⁿ-a.e. y ∈ E, ξ₂(y) = σ'ξ₁(y) for some σ' ∈ {±1}; then Σ_I ξ₁(y)(e^I)ξ₂(y)(e^I) = σ'Σ_I ξ₁(y)(e^I)² with Σ_I ξ₁(y)(e^I)² > 0 (step 5), so σ' = σ(y) := sign(Σ_I ξ₁(y)(e^I)·ξ₂(y)(e^I)), a Borel function, and ξ₂(y) = σ(y)ξ₁(y). The set of points of E where any of these properties fails is Hⁿ-null, hence contained in a Borel null set; let G ⊆ E be the Borel complement of that null set in E.
7. New data. On G put d := θ₁ − σθ₂ ∈ ℤ and G' := {y ∈ G : d(y) ≠ 0}. Define the Borel set M := (M₁ ∖ M₂) ∪ (M₂ ∖ M₁) ∪ G', the measurable m : ℝ^P → ℕ with m = θ₁ on M₁ ∖ M₂, m = θ₂ on M₂ ∖ M₁, m = |d| on G', m = 0 elsewhere, and the Borel ζ with ζ = ξ₁ on M₁ ∖ M₂, ζ = −ξ₂ on M₂ ∖ M₁, ζ = sign(d)ξ₁ on G', ζ = 0 elsewhere.
8. IMRep fields. M ⊆ M₁ ∪ M₂ ⊆ U; M is countably n-rectifiable (subset of the union of two countably n-rectifiable sets: SimonGMT CountablyRectifiable.mono, countablyRectifiable_iUnion); m ≥ 1 on M; m ≤ θ₁1_{M₁} + θ₂1_{M₂} (on G', |d| ≤ θ₁ + θ₂), so ∫_{M∩K} m dHⁿ ≤ ∫_{M₁∩K} θ₁ + ∫_{M₂∩K} θ₂ < ∞ for compact K ⊆ U; ζ is Borel, hence a.e. strongly measurable. Orientation property for Hⁿ-a.e. y ∈ M: (i) y ∈ M₁ ∖ M₂: M Δ M₁ ⊆ M₂ and, by F1 with A = M₂, M₂ has density 0 at a.e. y ∉ M₂, so F2 gives T_yM = T_yM₁, oriented by ξ₁(y) = ζ(y); (ii) y ∈ M₂ ∖ M₁: symmetrically T_yM = T_yM₂, oriented by ξ₂(y) and hence by ζ(y) = −ξ₂(y) (IsUnitOrientationOf allows either sign); (iii) y ∈ G': M Δ M₁ = (M₂ ∖ M₁) ∪ (E ∖ G') is a Borel set not containing y, so by F1 it has density 0 at a.e. such y, and F2 gives T_yM = T_yM₁, oriented by ξ₁(y) and hence by ζ(y) = ±ξ₁(y).
9. Representation. For ω ∈ 𝒟ⁿ(U) (all integrands are integrable, being bounded by (θ₁1_{M₁} + θ₂1_{M₂})·sup|ω|·1_{tsupport ω}): (S − T)(ω) = ∫_{M₁}θ₁ξ₁(ω) − ∫_{M₂}θ₂ξ₂(ω) = ∫_{M₁∖M₂}θ₁ξ₁(ω) + ∫_{M₂∖M₁}θ₂(−ξ₂)(ω) + ∫_E (θ₁ξ₁ − θ₂ξ₂)(ω) dHⁿ. On G, θ₁ξ₁ − θ₂ξ₂ = (θ₁ − σθ₂)ξ₁ = |d|·sign(d)ξ₁, which vanishes on G ∖ G', and E ∖ G is Hⁿ-null; so the last integral equals ∫_{G'} |d| sign(d)ξ₁(ω) dHⁿ. Hence (S − T)(ω) = ∫_M m ζ(ω) dHⁿ, i.e. (M, m, ζ) is an IMRep in U representing S − T, and S − T is integer multiplicity.

## Key steps

1. Upper Density Theorem: a set of locally finite Hⁿ-measure has density zero at Hⁿ-a.e. point outside it.
2. Approximate tangent spaces are unchanged by modifications of density zero, so on M₁ ∩ M₂ the tangent planes agree a.e. and ξ₂ = ±ξ₁.
3. Combine carriers: M₁∖M₂, M₂∖M₁ and the part of M₁∩M₂ where θ₁ξ₁ ≠ θ₂ξ₂, with integer multiplicities |θ₁ ∓ θ₂| and signed orientations.
4. Verify every IMRep field and the representation identity for S − T.

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
