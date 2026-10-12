# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.finite_net-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Steps 0, 1, 2(f) and the finite set 𝓑_ρ of Step 3 (Simon 7.2 proof, (1)–(3): "for T ∈ I_{M,W} we can find integer multiplicity P, R, S with (2), (3) … since there are only finitely many currents P as in (2), we have (1)"). Uses the siblings extend, restrict_im, lattice_chain_coeff, lattice_coeff_finite and top_dim_approx. MF and LC are passed to extend and top_dim_approx. This child is the parent's Steps 0–2 packaged with a uniform output; the pigeonhole step stays in the parent.

Notation. ι := testFormOnInclusion (subset_univ U) k; for Y ∈ D_k(ℝ^P), Y|_U := Y.restrictDomain (subset_univ U), so Y|_U(ω) = Y(ιω).

0. Inline facts.
   (Z1) The zero current 0 ∈ D_k(U) is integer multiplicity: take M := ∅, θ := 1, ξ := 0. The triple conditions hold: ∅ ⊆ U; ∅ is null-measurable; ∅ is countably k-rectifiable (countablyRectifiable_of_measure_zero); the pointwise conditions on ∅ are vacuous; IntegrableOn over ∅ holds; and a.e. statements for μHE[k]⌞∅ = 0 hold trivially. tauAction over ∅ is 0.
   (Z2) M(0) = 0, since every admissible evaluation is ofReal 0 = 0.
   (Z3) A lattice chain is determined by its coefficients: if IsLatticeChain ρ β Pc and IsLatticeChain ρ β Pc', then Pc(ω) = Σ'_F β(F) latticeFaceAction ρ F ω = Pc'(ω) for every ω, so Pc = Pc' (GeometricCurrentOn.ext).
   (Z4) Finite sets of centres. For a finite set 𝓑 of coefficient functions LatticeFaceIndex (m+1) P → ℝ, put 𝒬(𝓑) := {Pc|_U : β ∈ 𝓑, Pc ∈ D_{m+1}(ℝ^P), IsLatticeChain ρ β Pc}. Let Φ(β) be the restriction to U of a chosen lattice chain with coefficients β if one exists, and 0 otherwise. By (Z3), 𝒬(𝓑) ⊆ Φ(𝓑), which is finite. So 𝒬(𝓑) is finite.
   (Z5) For Y ∈ D_{q+1}(ℝ^P) and ω ∈ D^q(U), (Y|_U).boundary(ω) = (∂Y)(ιω), because the test forms d(ιω) and ι(dω) have the same underlying form dω. Also T(ω) = X(ιω) whenever X|_U = T.
   We distinguish three cases.
1. Case P < m + 1 (parent Step 0). Every Covector (ℝ^P) (m+1) is zero: for v : Fin (m+1) → ℝ^P, v is not linearly independent (otherwise m + 1 ≤ finrank ℝ^P = P, LinearIndependent.fintype_card_le_finrank, finrank_euclideanSpace_fin), so α(v) = 0 (AlternatingMap.map_linearDependent). Hence every ω ∈ D^{m+1}(U) has zero underlying form, ω = 0, and T(ω) = T(0) = 0 for every current T. Take C := 0 and 𝒬 := {0}; for T as in the statement take Q := 0, R := 0, S := 0. Then T(ω) − Q(ω) = 0 = ∂R(ω) + S(ω); R and S are integer multiplicity by (Z1); M(R) + M(S) = 0 ≤ 0 by (Z2).
2. Case P = m + 1 (parent Step 2). Substitute P := m + 1. Let c be the constant of the sibling top_dim_approx (applied with MF and LC) for this m, and put C := c. Fix B < ∞ and ρ > 0. Y_ρ := cthickening(√(m+1) ρ, K) is bounded (K is compact, hence bounded; Bornology.IsBounded.cthickening). Let A := 2 B.toReal / ρ^{m+1} and 𝓑 := {β : every β(F) is an integer, and β(F) ≠ 0 ⟹ latticeFace ρ F ⊆ Y_ρ and |β(F)| ≤ A}, finite by the sibling lattice_coeff_finite. Put 𝒬 := 𝒬(𝓑), finite by (Z4).
   Let T be as in the statement. The sibling extend (with MF, U, K; its hypothesis M(T) < ∞ holds because M(T) ≤ M(T) + M(∂T) ≤ B < ∞) gives X ∈ D_{m+1}(ℝ^{m+1}) with X|_U = T, spt X ⊆ K, M(X) ≤ M(T) ≤ B < ∞, M(∂X) ≤ M(∂T) ≤ B < ∞, and X integer multiplicity. top_dim_approx(X, ρ) gives β, Pc, S̃ with IsLatticeChain ρ β Pc, all β(F) integers, latticeFace ρ F ⊆ cthickening(√(m+1) ρ, spt X) ⊆ Y_ρ whenever β(F) ≠ 0 (cthickening_subset_of_subset), ofReal(|β(F)| ρ^{m+1}) ≤ 2M(X) ≤ 2B, S̃ integer multiplicity, X − Pc = S̃ and M(S̃) ≤ c ρ M(∂X). From ofReal(|β(F)| ρ^{m+1}) ≤ 2B with 2B ≠ ∞ we get |β(F)| ρ^{m+1} ≤ 2B.toReal (ENNReal.ofReal_le_iff_le_toReal), so |β(F)| ≤ A; hence β ∈ 𝓑.
   Take Q := Pc|_U ∈ 𝒬, R := 0 ∈ D_{m+2}(U) and S := S̃|_U. R is integer multiplicity (Z1), and S is integer multiplicity by the sibling restrict_im (W := U open, Y := S̃). For ω ∈ D^{m+1}(U): T(ω) − Q(ω) = X(ιω) − Pc(ιω) = S̃(ιω) = S(ω) = ∂0(ω) + S(ω). Mass: M(R) + M(S) = 0 + M(S̃|_U) ≤ M(S̃) (restrict_im) ≤ c ρ M(∂X) ≤ c ρ B.
3. Case P ≥ m + 2 (parent Step 1). Write P = m + 1 + ℓ with ℓ ≥ 1 and substitute (all data now live in ℝ^{m+1+ℓ}). Let C be the constant of DeformationTheorem for (m, ℓ). Fix B < ∞ and ρ > 0. Y_ρ := cthickening(2√P ρ, K) (bounded), A := C·B.toReal / ρ^{m+1}, 𝓑 as in case 2 with these Y_ρ and A (finite by lattice_coeff_finite), and 𝒬 := 𝒬(𝓑).
   Let T be as in the statement. extend (applicable because M(T) ≤ M(T) + M(∂T) ≤ B < ∞) gives X with X|_U = T, spt X ⊆ K, M(X) + M(∂X) ≤ M(T) + M(∂T) ≤ B < ∞, and X, ∂X integer multiplicity. DeformationTheorem applied to X and ρ gives Pc, β, R̃ ∈ D_{m+2}(ℝ^P) and S̃ ∈ D_{m+1}(ℝ^P) with IsLatticeChain ρ β Pc, X − Pc = ∂R̃ + S̃, M(Pc) ≤ C M(X), M(R̃) ≤ C ρ M(X), M(S̃) ≤ C ρ M(∂X), spt Pc ∪ spt R̃ ⊆ thickening(2√P ρ, spt X); since X is integer multiplicity, every β(F) is an integer and R̃ is integer multiplicity; since X and ∂X are integer multiplicity, S̃ is integer multiplicity.
   β ∈ 𝓑: if β(F) ≠ 0, the sibling lattice_chain_coeff (with m and N := P) gives latticeFace ρ F ⊆ spt Pc ⊆ thickening(2√P ρ, spt X) ⊆ cthickening(2√P ρ, spt X) ⊆ Y_ρ (spt X ⊆ K), and ofReal(|β(F)| ρ^{m+1}) ≤ M(Pc) ≤ C M(X) ≤ C B, so |β(F)| ≤ A as in case 2.
   Take Q := Pc|_U ∈ 𝒬, R := R̃|_U, S := S̃|_U, integer multiplicity by restrict_im. For ω ∈ D^{m+1}(U): T(ω) − Q(ω) = X(ιω) − Pc(ιω) = ∂R̃(ιω) + S̃(ιω) = ∂R(ω) + S(ω) by (Z5). Mass: M(R) + M(S) ≤ M(R̃) + M(S̃) (restrict_im) ≤ C ρ M(X) + C ρ M(∂X) = C ρ (M(X) + M(∂X)) ≤ C ρ B.
4. In each case the required C and, for each B < ∞ and ρ > 0, the finite set 𝒬 have been produced. ∎

Remark (adaptable accepted Lean proof; optional). The vanishing used in case 1 is the comparator-accepted Submission.br_la_apply_eq_zero_of_lt_degree (commit 5e97e54b7c48d8e53196b85846b7863fbaa0fe66): ∀ (P n : ℕ) (U : Set (Eucl P)) (X : GeometricCurrentOn U n), P < n → ∀ ω : TestFormOn U n, X ω = 0. Its Lean proof may be copied under a fresh name.

## Key steps

1. P < m + 1: all test forms of degree m + 1 vanish, so T = 0; take C = 0, 𝒬 = {0}, R = S = 0.
2. P = m + 1: extend T to X on ℝ^{m+1}, apply top_dim_approx at scale ρ, take Q = Pc|_U, R = 0, S = S̃|_U.
3. P ≥ m + 2: extend T to X, apply DeformationTheorem at scale ρ, and use lattice_chain_coeff to bound the faces and coefficients; take Q = Pc|_U, R = R̃|_U, S = S̃|_U.
4. In both nontrivial cases β lies in a set 𝓑 that is finite by lattice_coeff_finite, and lattice chains are determined by their coefficients, so the centres form a finite set.
5. restrict_im gives integer multiplicity and the mass bounds of the restricted R, S, so M(R) + M(S) ≤ CρB.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c95, Mathlib 25730c7c)`
- `python3 scan of dag.json (235 nodes): no lean_name containing fiw_tb; frozen lean_statement of root.flat_iff_weak-a1.im_mass_formula-a1 (accepted) and im_lincomb-a1 compared textually with the MF/LC premises`
- `git log --all --oneline -S fiw_tb_ (687 refs, no match); grep -rl fiw_tb_ .humanize/math-wiki (no match)`
- `git show <commit>:GMT/Ch06/Submission.lean | grep -c 'theorem Submission.<name>' for the 12 cited accepted declarations (all present), including br_la_abs_apply_le_mul_mass @ d771ac3a and fiw_ims_frame_sign @ c90a4050`
- `grep -n max_nodes /runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/runtime.py; read _decompose, _solve_children, _existing_lean_name_problem; swarm-configs/8d6f8e1fdf494359a56bc7f71c57d439.json (max_nodes 1000, max_children 12, max_depth 6)`
- `grep -n 'def covectorEuclideanNorm|def massAdmissibleOn|def GeometricCurrentOn.massOn|def TestFormOnConverges|structure GeometricCurrentOn|zero_apply|boundary_apply|restrictDomain_apply|def testFormOnInclusion|def GeometricCurrentOn.zeroRegion|def GeometricCurrentOn.support|abbrev SimonMultiIndex|def CountablyRectifiable|countablyRectifiable_of_measure_zero|def blowUpMap|def HasWeightedApproximateTangentSpaceAt' in SimonGMT Chapter06/Chapter03`
- `grep Mathlib: theorem exists_nnreal_pos_mul_lt, Finite.exists_infinite_fiber, Infinite.exists_ne_map_eq_of_mapsTo, thickening_subset_of_subset, cthickening_subset_of_subset, thickening_subset_cthickening, mul_le_mul_right`
- `lake build GMT.Ch06.Submission in /tmp/tb5-Hq3Nws (git archive d8d46c9, packages linked)`
- `python3 -I /tmp/tb5_tools/gen_challenges.py (verifier/gmt-compare.py child_modules mode contract + lean_contract.validate_lean_statement); lake env lean Scratch/V4/Ch_*.lean and Scratch/V4/Remaining3.lean (0 errors)`
- `lake env lean Scratch/V4/Assembly.lean and Scratch/V4/FiniteNet.lean (#print axioms: propext, Classical.choice, Quot.sound)`
- `sed -n 2028,2090p book/chapter-06.txt (Simon 7.2 and its proof, (1)–(3))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1/decomposition-audit-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/swarm-configs/8d6f8e1fdf494359a56bc7f71c57d439.json`
- `/runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/math-wiki/submission-br-la-abs-apply-le-mul-mass.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/math-wiki/submission-fiw-ims-frame-sign.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/math-wiki/submission-fiw-im-mass-formula.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Data/Fintype/Pigeonhole.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/tb5-Hq3Nws/Scratch/V4/Assembly.lean`
- `/tmp/tb5-Hq3Nws/Scratch/V4/FiniteNet.lean`
- `/tmp/tb5-Hq3Nws/Scratch/V4/Remaining3.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract (IsIntegerMultiplicity, IsRectifiableTriple, tauAction, latticeFace, latticeFaceAction, IsLatticeChain, DeformationTheorem). Neither the project nor SimonGMT has an integer-multiplicity calculus, a flat-norm lemma or a lattice-chain coefficient bound, so these become the 10 children.

SimonGMT supplies the API used in the child proofs:
- massOn and mass via massAdmissibleOn and covectorEuclideanNorm, and le_massOn / massOn_mono;
- restrictDomain(_apply), testFormOnInclusion, zero_apply, boundary_apply and GeometricCurrentOn.ext;
- zeroRegion and support = U \ zeroRegion;
- SimonMultiIndex = Fin n ↪o Fin p, CountablyRectifiable (with countablyRectifiable_of_measure_zero and .mono), blowUpMap and HasWeightedApproximateTangentSpaceAt.
Mathlib supplies ENNReal.exists_nnreal_pos_mul_lt and the thickening lemmas.

Accepted Submission declarations, cited in the remarks as optional reuse pointers, were checked at their commits. The two new pointers are:
- br_la_abs_apply_le_mul_mass (d771ac3a), the evaluation bound;
- fiw_ims_frame_sign (c90a4050), the frame sign.

Scratch checks:
- all 10 child types elaborate in the comparator's exact challenge scope;
- the parent type follows from MF, LC, fiw_tb_finite_net and fiw_tb_flat_sub;
- fiw_tb_finite_net follows from its five siblings;
- both derivations use only [propext, Classical.choice, Quot.sound].
