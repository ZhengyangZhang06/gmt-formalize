# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.localize-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof ("a competitor S' for T' in W ⊂⊂ U' differs from T' by a compactly supported current, so S := T + (S' − T') (extension by zero) is an integer multiplicity competitor for T with the same boundary and the same masses difference on W"), with the details supplied. Uses the siblings vanish_off_support (V), mass_eq_measure (M) and im_sub (G). Since n ≥ 1, spt ∂T = spt(T.boundary) and BoundaryVanishes T' means T'.boundary = 0.
1. (a) spt ∂T = U ∖ Z_∂, where Z_∂ is the zero region of ∂T, a union of open sets whose closures lie in U; so Z_∂ is open and Z_∂ ⊆ U, and U' = U ∖ (U ∖ Z_∂) = Z_∂ is open.
2. (e) Let W ⊆ U'. A form ω ∈ 𝒟ⁿ(U) with tsupport ω ⊆ W ⊆ U' lies in 𝒟ⁿ(U') and conversely, and T'(ω) = T(ω) by the definition of restrictDomain. So the admissible families defining M_W(T') and M_W(T) correspond bijectively with equal values, and M_W(T') = M_W(T).
3. (d) Let y ∈ U' ∖ spt T. Then y lies in an open V with compact closure in U on which T vanishes. Choose r > 0 with closedBall(y, r) ⊆ U' (U' open) and put V' := V ∩ ball(y, r): V' is open, y ∈ V', closure V' ⊆ closedBall(y, r) is compact and ⊆ U', and T' vanishes on V' (a form in 𝒟ⁿ(U') supported in V' is a form in 𝒟ⁿ(U) supported in V). So y ∉ spt T'. As spt T' ⊆ U', spt T' ⊆ spt T.
4. (c) For ω ∈ 𝒟^{n−1}(U'): ∂T'(ω) = T'(dω) = T(dω) = ∂T(ω), with ω regarded in 𝒟^{n−1}(U). Since tsupport ω ⊆ U' = U ∖ spt ∂T is disjoint from spt ∂T, V applied to the current ∂T gives ∂T(ω) = 0. Hence ∂T' = 0.
5. (b), integer multiplicity of T'. Let R = (M, θ, ξ) represent T and R' := (M ∩ U', θ, ξ). This is an IMRep in U': M ∩ U' is Borel (U' open) and ⊆ U'; it is countably n-rectifiable (subset of M); measurability, positivity and integrability over compact subsets of U' ⊆ U are inherited; orientation: if y ∈ M ∩ U' and HasApproximateTangentSpaceAt n M y Q, choose s > 0 with B_s(y) ⊆ U'; for f ∈ C_c with spt f ⊆ B_L(0) and r < s/L the sets η_{y,r}(M) and η_{y,r}(M ∩ U') agree on B_L(0), so the blow-up integrals agree and HasApproximateTangentSpaceAt n (M ∩ U') y Q, still oriented by ξ(y). Representation: for ω ∈ 𝒟ⁿ(U'), T'(ω) = T(ω) = ∫_M θξ(ω) = ∫_{M∩U'} θξ(ω) because ω vanishes off U'. So T' is integer multiplicity.
6. (b), comparison. Let W be open with closure W compact and ⊆ U', S' ∈ 𝒟_n(U') integer multiplicity with ∂S' = ∂T', and K := spt(S' − T') compact with K ⊆ A ∩ W. Put X := S' − T' ∈ 𝒟_n(U').
 6.1 X is integer multiplicity by G (U' open, n ≥ 1), and ∂X = ∂S' − ∂T' = 0.
 6.2 Since closure W is a compact subset of the open set U', choose an open O and χ ∈ C_c^∞(U') with closure W ⊆ O, 0 ≤ χ ≤ 1 and χ = 1 on O (smooth Urysohn lemma). Define X̃ ∈ 𝒟_n(U) by X̃(ω) := X(χω); χω ∈ 𝒟ⁿ(U') because tsupport(χω) ⊆ tsupport χ, a compact subset of U'. X̃ is linear, and continuous: if ω_j → 0 in 𝒟ⁿ(U) then χω_j → 0 in 𝒟ⁿ(U') (supports in tsupport χ, Leibniz rule for derivatives), so X̃(ω_j) → 0.
 6.3 X̃(ω) = X(ω) for every ω ∈ 𝒟ⁿ(U'): X(ω) − X(χω) = X((1 − χ)ω), where (1 − χ)ω ∈ 𝒟ⁿ(U') and tsupport((1 − χ)ω) ⊆ closure{χ ≠ 1}, which is disjoint from the open set O ⊇ K; by V, X((1 − χ)ω) = 0.
 6.4 ∂X̃ = 0: for ω ∈ 𝒟^{n−1}(U), d(χω) = dχ ∧ ω + χ dω, so ∂X̃(ω) = X̃(dω) = X(χ dω) = X(d(χω)) − X(dχ ∧ ω) = ∂X(χω) − X(dχ ∧ ω) = −X(dχ ∧ ω); dχ ∧ ω ∈ 𝒟ⁿ(U') has tsupport ⊆ tsupport(dχ) ⊆ ℝ^P ∖ O (dχ = 0 on the open set O), disjoint from K, so X(dχ ∧ ω) = 0 by V.
 6.5 spt X̃ ⊆ K and spt X̃ is compact: if q ∈ U ∖ K, choose a ball B ∋ q with closure compact and ⊆ U ∖ K (open); for ω ∈ 𝒟ⁿ(U) with tsupport ω ⊆ B, tsupport(χω) ⊆ B is disjoint from K, so X̃(ω) = X(χω) = 0 by V; thus q ∉ spt X̃. spt X̃ is relatively closed in U and contained in the compact K ⊆ U, hence closed in K and compact.
 6.6 X̃ is integer multiplicity. Let R_X = (M_X, θ_X, ξ_X) represent X in U'. Every admissible form ω for U' ∖ K (open, ⊆ U') has tsupport disjoint from K = spt X, so X(ω) = 0 by V and M_{U'∖K}(X) = 0; by M, μ_{R_X}(U' ∖ K) = 0, and since θ_X ≥ 1, Hⁿ(M_X ∖ K) = 0. Then R̃ := (M_X ∩ K, θ_X, ξ_X) is an IMRep in U: M_X ∩ K is Borel and ⊆ K ⊆ U; integrability over compact sets holds because ∫_{M_X∩K} θ_X < ∞ (K compact ⊆ U'); the blow-up integrals ∫_{η_{y,r}(·)} f dHⁿ of M_X and M_X ∩ K coincide for all y, r (they differ by the image of an Hⁿ-null set, which is null), so they have the same approximate tangent spaces, oriented by ξ_X; and X̃(ω) = X(χω) = ∫_{M_X} θ_X χ ξ_X(ω) = ∫_{M_X∩K} θ_X ξ_X(ω) since Hⁿ(M_X ∖ K) = 0 and χ = 1 on K.
 6.7 The competitor. The zero current is integer multiplicity (empty carrier), so by G the current Y := 0 − X̃ is integer multiplicity, and again by G, S := T − Y is integer multiplicity; S(ω) = T(ω) + X̃(ω).
 6.8 Admissibility for T: W is open with closure W compact ⊆ U' ⊆ U; ∂S = ∂T + ∂X̃ = ∂T by 6.4; S − T = X̃, so spt(S − T) = spt X̃ is compact and ⊆ K ⊆ A ∩ W by 6.5.
 6.9 Minimality of T gives M_W(T) ≤ M_W(S). For ω ∈ 𝒟ⁿ(U) with tsupport ω ⊆ W ⊆ U', by 6.3, S(ω) = T(ω) + X(ω) = T'(ω) + S'(ω) − T'(ω) = S'(ω). As in step 2 the admissible families on W for S and S' (and for T and T') correspond with equal values, so M_W(S) = M_W(S') and M_W(T) = M_W(T'). Hence M_W(T') ≤ M_W(S'), and T' is minimizing in A.

## Key steps

1. U ∖ spt ∂T is the open zero region of ∂T; masses on subsets agree and spt T' ⊆ spt T; ∂T' = 0 by the support lemma.
2. T' is integer multiplicity: restrict a representation of T to the open set U'.
3. Given a competitor S' for T', extend X = S' − T' by zero with a cutoff; X̃ is integer multiplicity (its carrier is null off spt X by mass_eq_measure) with ∂X̃ = 0 and spt X̃ = spt X.
4. S = T + X̃ is an integer multiplicity competitor for T agreeing with S' on W, so minimality of T transfers to T'.

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
