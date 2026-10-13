# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tangent_projection_measurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: this measurability is used implicitly throughout Simon, Ch. 3–5 (the approximate tangent space of a rectifiable set is Hⁿ-measurable, and integrals such as ∫div_M X dμ, ∫|p_x − p_S|²dμ presuppose it); the parent proof uses it whenever it integrates functions of p_x. The proof below derives it from the IMRep fields.

1. Notation and reduction. E := ℝ^P (Lean Euclid P) with inner product ⟨·,·⟩; M := R.carrier; ν := Hⁿ⌞M (Lean μHE[n].restrict R.carrier); R.measure = ν.withDensity θ, so R.measure ≪ ν (withDensity_absolutelyContinuous). Hence it suffices to show that x ↦ p_{T_xM} := (approxTangentPlane n M x).starProjection is AE-strongly measurable with respect to ν (then AEStronglyMeasurable.mono_ac gives the claim for R.measure). For a submodule Q, p_Q := Q.starProjection is the orthogonal projection onto Q, an element of the finite-dimensional normed space End(E) := E →L[ℝ] E. The orientation ξ := R.orient takes values in MultiVector P n, the (finite-dimensional) normed space of continuous linear functionals on Covector E n (continuous alternating n-linear forms E^n → ℝ); IsUnitOrientationOf η Q means: there are τ = (τ₁,…,τₙ) orthonormal with span{τ_m} = Q and s ∈ {1, −1} such that η(β) = s·β(τ₁,…,τₙ) for every β ∈ Covector E n. By the IMRep field aestronglyMeasurable_orient, ξ is AE-strongly measurable with respect to ν.

2. Identification of T_xM. By the IMRep field orients there is a ν-null set N₁ such that for every x ∉ N₁ some submodule Q_x satisfies HasApproximateTangentSpaceAt n M x Q_x and IsUnitOrientationOf (ξ x) Q_x. For such x the existential condition in the definition of approxTangentPlane holds, so approxTangentPlane n M x is a submodule Q' with HasApproximateTangentSpaceAt n M x Q'; by uniqueness of approximate tangent planes (Simon Ch. 3, Remark 1.5(1); library HasApproximateTangentSpaceAt.unique) Q' = Q_x. Hence p_{T_xM} = p_{Q_x} for every x ∉ N₁.

3. Case n = 0. Every submodule of finrank 0 is ⊥, and approxTangentPlane 0 M x = ⊥ in both branches of its definition (an approximate tangent plane has finrank n = 0). So the map is the constant 0, which is strongly measurable. Assume n ≥ 1 from now on.

4. A unit simple n-vector determines its plane. Let η ∈ MultiVector P n satisfy η(β) = s·β(τ₁,…,τₙ) for all β, with τ orthonormal and s = ±1. Claim: span τ = {v ∈ E : η(ι_vγ) = 0 for every γ ∈ Covector E (n+1)}, where ι_vγ ∈ Covector E n is (u₁,…,uₙ) ↦ γ(v, u₁,…,uₙ). If v ∈ span τ then η(ι_vγ) = s·γ(v, τ₁,…,τₙ) = 0, because the n + 1 arguments are linearly dependent and γ is alternating. If v ∉ span τ, let w := v − Σ_i⟨v, τ_i⟩τ_i ≠ 0 (w ⊥ τ_i) and γ(u₀,…,uₙ) := det(⟨c_a, u_b⟩)_{a,b=0..n} with c := (w, τ₁,…,τₙ); γ is a continuous alternating (n+1)-form. The matrix (⟨c_a, u_b⟩) for (u₀,…,uₙ) := (v, τ₁,…,τₙ) has first row (⟨w, v⟩, ⟨w, τ₁⟩,…) = (|w|², 0,…,0) and lower-right n×n block (⟨τ_a, τ_b⟩) = I_n, so γ(v, τ₁,…,τₙ) = |w|² and η(ι_vγ) = s|w|² ≠ 0. Consequently, if IsUnitOrientationOf η Q and IsUnitOrientationOf η Q', then Q = Q' (both equal the set above).

5. A Borel map Ĝ : MultiVector P n → End(E) with Ĝ(η) = p_Q whenever IsUnitOrientationOf η Q. Let Ω := {(τ, s) : τ ∈ E^n orthonormal, s ∈ {1, −1}}; it is compact (closed and bounded in E^n × ℝ). Ψ(τ, s) := (β ↦ s·β(τ₁,…,τₙ)) defines a continuous map Ω → MultiVector P n (the evaluation pairing (β, τ) ↦ β(τ) is continuous and multilinear, and |β(τ)| ≤ ‖β‖ when |τ_i| = 1). Its image 𝒮 := Ψ(Ω) is compact, hence closed, and equals {η : ∃ Q, IsUnitOrientationOf η Q}. The map G̃(τ, s) := p_{span τ} = Σ_i⟨τ_i, ·⟩τ_i is continuous on Ω, and by 4 it is constant on the fibres of Ψ; hence G̃ = G ∘ Ψ for a unique G : 𝒮 → End(E). Since Ψ : Ω → 𝒮 is a continuous surjection from a compact space onto a Hausdorff space, it is a closed map, hence a quotient map, so G is continuous on 𝒮. Let Ĝ := G on 𝒮 and Ĝ := 0 off 𝒮; Ĝ is Borel measurable (𝒮 is closed and G is continuous on it), and Ĝ(η) = p_Q whenever IsUnitOrientationOf η Q.

6. Conclusion. ξ is AE-strongly measurable for ν, hence AE-measurable (MultiVector P n is finite dimensional, so second countable with its Borel σ-algebra), and Ĝ is Borel, so Ĝ ∘ ξ is ν-AE-measurable; End(E) is finite dimensional (second countable, metrizable), so Ĝ ∘ ξ is ν-AE-strongly measurable. By 2 and 5, Ĝ(ξ x) = p_{Q_x} = p_{T_xM} for every x ∉ N₁, so x ↦ (approxTangentPlane n M x).starProjection agrees ν-a.e. with Ĝ ∘ ξ and is ν-AE-strongly measurable (AEStronglyMeasurable.congr). By 1, it is AE-strongly measurable with respect to R.measure. ∎

## Key steps

1. Reduce to Hⁿ⌞M: R.measure = (Hⁿ⌞M).withDensity θ is absolutely continuous w.r.t. Hⁿ⌞M (mono_ac).
2. For Hⁿ⌞M-a.e. x, approxTangentPlane n M x is the plane Q_x oriented by orient x (IMRep.orients and uniqueness of approximate tangent planes).
3. Case n = 0: the map is identically 0.
4. A unit simple n-vector determines its plane: span τ = {v : η(ι_vγ) = 0 for all (n+1)-covectors γ}, via the determinant form γ = det(⟨c_a, ·⟩).
5. The compact set Ω of orthonormal frames maps onto the closed set 𝒮 of unit simple n-vectors by a quotient map, so η ↦ p_Q is continuous on 𝒮; extending by 0 gives a Borel map Ĝ.
6. Ĝ ∘ orient is AE-strongly measurable and agrees a.e. with x ↦ p_{T_xM}.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (both identical)`
- `rg -n -i 'allard|tilt.?excess|harmonic.?approx|lipschitz.?approx' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `rg -n 'sorry' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean; rg -n '^theorem|^lemma' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `rg -l -i "rellich|kondrachov|weyl's lemma|weakly harmonic" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory  (no match, exit 1)`
- `rg -n 'theorem ae_differentiableAt|theorem norm_fderiv_le_of_lipschitz' Analysis/Calculus/Rademacher.lean Analysis/Calculus/FDeriv/Basic.lean; grep -n ae_differentiableAt Analysis/Calculus/Rademacher.lean  (in the snapshot Mathlib)`
- `rg -n 'theorem exists_disjoint_subfamily_covering_enlargement_closedBall' MeasureTheory/Covering/Vitali.lean; rg -n 'theorem ae_tendsto_average_norm_sub' MeasureTheory/Covering/Differentiation.lean; rg -n 'theorem measurable_fderiv' Analysis/Calculus/FDeriv/Measurable.lean  (in the snapshot Mathlib)`
- `sed -n 10,30p lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean (simongmt rev 2b3663083f3fe399b6296fb8eaee52169170e197 from the snapshot's lake-manifest.json)`
- `python3: lean_name collision scan of the 12 dorag_* names over dag.json (200 nodes), nodes/*/*.json and other workspaces' dag.json; exact-statement comparison against .humanize/math-wiki/*.md (43 pages)`
- `python3 -I lean_contract.validate_lean_statement on all 12 lean_statements; lean (lean-4.35.0-rc3, LEAN_PATH of the built workspace) on 13 comparator-format modules Challenge_<key>.lean`
- `lean Check.lean (#check of the Mathlib API used by the assembly); lean Assembly.lean with #print axioms GMT.Ch07.AllardAsmV3.assembly`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/math-wiki`
- `/tmp/allard-v3-work/v3/Challenge_PARENT.lean`
- `/tmp/allard-v3-work/asm3/Assembly.lean`
- `/tmp/allard-v3-work/asm3/Assembly.log`

The snapshot pins project b4d606d and Mathlib 25730c7c. Its GMT/Ch07/Contract.lean is byte-identical to the workspace contract and to GMT/Ch07/Submission.lean, which is the compiler context of every child type.

Nothing in the snapshot proves Allard regularity or any child:
- The only Allard-related declarations are in GMT/Ch05/Submission.lean: Prop definitions (TiltExcessHeightEstimate, AffineApproximationLemma, LipschitzApproximationLemma, HarmonicApproximationLemma, TiltExcessDecayTheorem, AllardRegularityTheorem, …) for a different varifold type. They are used only in main_theorem := by sorry (line 461), so nothing is proved there.
- SimonGMT Chapter05/Basic.lean says compactness, Lipschitz approximation, excess decay and Allard regularity are not formalized.
- The Rellich/Kondrachov/Weyl/weakly-harmonic search found no match in the snapshot's Mathlib Analysis and MeasureTheory.
The split into 12 children therefore stands, and no identical comparator-approved declaration exists to reuse.

The Mathlib tools the children cite exist at the pinned revision:
- LipschitzWith.ae_differentiableAt (Rademacher.lean:385);
- norm_fderiv_le_of_lipschitz (FDeriv/Basic.lean:947);
- measurable_fderiv (FDeriv/Measurable.lean:378);
- Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall (Vitali.lean:158);
- VitaliFamily.ae_tendsto_average_norm_sub (Differentiation.lean:837).

Lean checks:
- All 12 child types and the frozen parent type elaborate in comparator scope; the only diagnostic is the expected sorry warning.
- The assembly proves the exact parent type from the five top-level child types, with axioms propext, Classical.choice and Quot.sound only.
- No dorag_* name collides with any DAG reservation.
