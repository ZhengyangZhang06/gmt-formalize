# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. ℝⁿ = EuclideanSpace ℝ (Fin n) with Euclidean norm |·|. Lⁿ = volume is Lebesgue measure on ℝⁿ, a locally finite, weakly regular additive Haar measure. (ℝⁿ)* = L(ℝⁿ, ℝ) carries the operator norm ‖·‖. For x ∈ ℝⁿ let Dg(x) := fderiv ℝ g x ∈ (ℝⁿ)*; by Mathlib's convention Dg(x) = 0 where g is not differentiable. For y ≠ x let R(x,y) := (g(y) − g(x) − Dg(x)(y − x))/|y − x|.

Source. This is Simon, Ch. 2, Theorem 1.5 (C¹ Approximation Theorem), in the stronger form that Simon's printed proof (p. 44) actually establishes: a closed set A on which g is differentiable. Printed proof: “By Rademacher's Theorem f is differentiable on a set B ⊆ ℝⁿ with Lⁿ(ℝⁿ ∖ B) = 0. By Lusin's theorem (which applies to sets of infinite measure for Lⁿ) there is a closed set C ⊆ B such that ∇f|C is continuous and Lⁿ(ℝⁿ ∖ C) < ε/2. On C we define h(x) = f(x), τ(x) = ∇f(x) and R(x,y) for x, y ∈ C is as defined in 1.6 (‡). Evidently (since C ⊆ B) we have lim_{y→x, y∈C} R(x,y) = 0 ∀ x ∈ C, but not necessarily uniformly with respect to x on compact subsets of C as in 1.6 (‡). We therefore proceed as follows. For each k = 1, 2, … let η_k(x) = sup{|R(x,y)| : y ∈ C ∩ B_{1/k}(x) ∖ {x}}. Then η_k ↓ 0 pointwise in C, and hence by Egoroff's Theorem (applied to the finite measure sets C ∩ B_j(0), j = 1, 2, …) there is an Lⁿ-measurable set A₀ ⊆ C such that Lⁿ(C ∖ A₀) < ε/4 and η_k converges uniformly to zero on each bounded subset of A₀. Since we can take a closed set A ⊆ A₀ with Lⁿ(A₀ ∖ A) < ε/4 we thus have Lⁿ(ℝⁿ ∖ A) < ε and 1.6 (‡) holds. Hence we can apply the Whitney Theorem 1.6, and the proof is complete.”

The numbered proof below is this printed proof with every step filled in. The infinite-measure uses of Lusin's theorem and of closed inner approximation, and Egoroff's theorem, are all carried out on bounded open annuli.

1. (Reductions and annuli.)
- If ε > 1, in particular if ε = ∞, replace ε by 1: a set A with Lⁿ(ℝⁿ ∖ A) < 1 also has Lⁿ(ℝⁿ ∖ A) < ε. So assume 0 < ε ≤ 1.
- Let S₁ := {x : |x| < 1} and S_j := {x : j − 1 < |x| < j} for j ≥ 2. The S_j are open, pairwise disjoint and bounded, so Lⁿ(S_j) < ∞.
- Z := ℝⁿ ∖ ⋃_j S_j = ⋃_{j≥1} {x : |x| = j} is a countable union of spheres of nonzero radius, so Lⁿ(Z) = 0 (Mathlib MeasureTheory.Measure.addHaar_sphere_of_ne_zero; for n = 0 these spheres are empty).
- Gluing fact (★), closedness: if F_j ⊆ S_j is closed for every j ≥ 1, then F := ⋃_j F_j is closed. The family (F_j) is locally finite, since the ball {|x| < r} meets S_j only if j − 1 < r (Mathlib LocallyFinite.isClosed_iUnion).
- Gluing fact (★), continuity: if a map φ is continuous on every F_j, then φ is continuous on F. Each x ∈ F_j has the open neighbourhood S_j with S_j ∩ F = F_j, because the S_l are pairwise disjoint. So near x the restriction of φ to F coincides with its restriction to F_j.

2. (Rademacher.) g is K-Lipschitz, so by Rademacher's theorem (Simon Ch. 2, Theorem 1.4; Mathlib LipschitzWith.ae_differentiableAt; SimonGMT rademacher_ae_differentiableAt) the set D := {x : g is differentiable at x} has Lⁿ(ℝⁿ ∖ D) = 0. D is Borel (Mathlib measurableSet_of_differentiableAt), and x ↦ Dg(x) is Borel measurable (Mathlib measurable_fderiv). For x ∈ D we have ‖Dg(x)‖ ≤ K, because |Dg(x)v| = lim_{t→0} |g(x + tv) − g(x)|/|t| ≤ K|v| (Mathlib norm_fderiv_le_of_lipschitz).

3. (Lusin's theorem for Lⁿ on all of ℝⁿ.) Claim: there is a closed C ⊆ D such that Dg is continuous on C and Lⁿ(ℝⁿ ∖ C) ≤ ε/4 < ε/2.
- Let e₁, …, e_n be the standard basis of ℝⁿ and fix j ≥ 1. S_j ∩ D is Borel and has finite measure.
- By inner regularity of Lⁿ by closed sets (Mathlib MeasurableSet.exists_isClosed_sdiff_lt) there is a closed F_j ⊆ S_j ∩ D with Lⁿ((S_j ∩ D) ∖ F_j) < ε/2^{j+3}.
- For l = 1, …, n the real function x ↦ Dg(x)e_l is Borel measurable. Lusin's theorem on the finite-measure set S_j ∩ D gives a closed C_{j,l} ⊆ S_j ∩ D with Lⁿ((S_j ∩ D) ∖ C_{j,l}) < ε/(2^{j+3}(n+1)) on which x ↦ Dg(x)e_l is continuous. Here Lusin is Simon Ch. 1, Theorem 1.17, i.e. SimonGMT Poincare.SimonGMT.Chapter01.exists_isClosed_continuousOn_of_measurable from the built module Poincare.SimonGMT.Chapter01.Lusin, which must be imported explicitly. Its closed-inner-approximation hypothesis for Lⁿ is again MeasurableSet.exists_isClosed_sdiff_lt.
- Put C_j := F_j ∩ ⋂_{l=1}^{n} C_{j,l} (C_j = F_j if n = 0). Then C_j is closed and C_j ⊆ S_j ∩ D.
- Its measure defect is Lⁿ((S_j ∩ D) ∖ C_j) < ε/2^{j+3} + n·ε/(2^{j+3}(n+1)) < ε/2^{j+2}.
- Dg is continuous on C_j, because all its coordinates are: λ ↦ (λ(e₁), …, λ(e_n)) is a linear homeomorphism (ℝⁿ)* → ℝⁿ.
- Let C := ⋃_j C_j. By (★), C is closed and Dg is continuous on C; also C ⊆ D.
- Since ℝⁿ ∖ C ⊆ Z ∪ (ℝⁿ ∖ D) ∪ ⋃_j ((S_j ∩ D) ∖ C_j), we get Lⁿ(ℝⁿ ∖ C) ≤ 0 + 0 + Σ_{j≥1} ε/2^{j+2} = ε/4.

4. (The functions η_k.) For k ≥ 1 and x ∈ C let η_k(x) := sup({|R(x,y)| : y ∈ C, 0 < |y − x| < 1/k} ∪ {0}); for x ∉ C let η_k(x) := 0.
(a) Bounds. For x ∈ C ⊆ D and y ≠ x, |R(x,y)| ≤ |g(y) − g(x)|/|y − x| + ‖Dg(x)‖ ≤ 2K. Hence 0 ≤ η_k ≤ 2K and η_k is real-valued.
(b) Convergence. η_{k+1} ≤ η_k, and η_k(x) → 0 for every x ∈ C. Given δ > 0, differentiability of g at x ∈ D gives ρ > 0 with |g(y) − g(x) − Dg(x)(y − x)| ≤ δ|y − x| whenever |y − x| < ρ. So η_k(x) ≤ δ once 1/k ≤ ρ.
(c) Measurability: η_k is Borel measurable.
- For fixed y ∈ C let φ_y : C → [0, ∞) be φ_y(x) := |R(x,y)| if 0 < |x − y| < 1/k, and φ_y(x) := 0 otherwise.
- φ_y is lower semicontinuous on C. The set U_y := {x ∈ C : 0 < |x − y| < 1/k} is relatively open in C, and φ_y is continuous on U_y: g is continuous, Dg is continuous on C by step 3, and |y − x| > 0 on U_y. This gives lower semicontinuity at points of U_y. At x₀ ∈ C ∖ U_y we have φ_y(x₀) = 0 ≤ φ_y(x) for all x ∈ C.
- As φ_y ≥ 0, η_k|C = sup_{y∈C} φ_y is a pointwise supremum of lower semicontinuous functions, hence lower semicontinuous on C.
- So each set {x ∈ C : η_k(x) > t} (t ∈ ℝ) is relatively open in the closed set C, hence Borel. Since η_k vanishes off C, η_k is Borel measurable on ℝⁿ.
- Equivalent route: if C′ ⊆ C is countable and dense in C, then η_k(x) = sup_{y∈C′} φ_y(x) for x ∈ C. This holds because y ↦ R(x,y) is continuous at every y ≠ x and the condition 0 < |y − x| < 1/k is open in y. So η_k is a countable supremum of Borel functions.

5. (Egoroff on bounded pieces.) Fix j ≥ 1.
- C_j = C ∩ S_j is Borel with Lⁿ(C_j) ≤ Lⁿ(S_j) < ∞. Every η_k is Borel measurable by 4(c), and η_k → 0 at every point of C_j by 4(b).
- By Egoroff's theorem (Mathlib MeasureTheory.tendstoUniformlyOn_of_ae_tendsto) there is a measurable T_j ⊆ C_j with Lⁿ(T_j) ≤ ε/2^{j+3} such that η_k → 0 uniformly on C_j ∖ T_j.
- Put A₀ := ⋃_j (C_j ∖ T_j) ⊆ C. Since C = ⋃_j C_j, we have C ∖ A₀ ⊆ ⋃_j T_j, so Lⁿ(C ∖ A₀) ≤ Σ_{j≥1} ε/2^{j+3} = ε/8.

6. (A closed A ⊆ A₀.)
- For every j, C_j ∖ T_j is measurable with finite measure. By inner regularity (MeasurableSet.exists_isClosed_sdiff_lt) there is a closed A_j ⊆ C_j ∖ T_j with Lⁿ((C_j ∖ T_j) ∖ A_j) < ε/2^{j+3}.
- Let A := ⋃_j A_j. Since A_j ⊆ C_j ⊆ S_j, A is closed by (★).
- A ⊆ A₀ ⊆ C ⊆ D and A₀ ∖ A ⊆ ⋃_j ((C_j ∖ T_j) ∖ A_j), so Lⁿ(A₀ ∖ A) ≤ ε/8.
- As ℝⁿ ∖ A ⊆ (ℝⁿ ∖ C) ∪ (C ∖ A₀) ∪ (A₀ ∖ A), we get Lⁿ(ℝⁿ ∖ A) ≤ ε/4 + ε/8 + ε/8 = ε/2 < ε.
- Uniformity on bounded sets: suppose W ⊆ {|x| < J} with J ∈ ℕ. Then W ∩ A ⊆ ⋃_{j≤J} (C_j ∖ T_j), because A_j ⊆ S_j ⊆ {|x| > j − 1} does not meet {|x| < J} when j > J. This is a finite union of sets on each of which η_k → 0 uniformly, so η_k → 0 uniformly on W ∩ A.

7. (Whitney's hypothesis (‡) on A.)
(i) g is Lipschitz, hence continuous on A.
(ii) Dg is continuous on A ⊆ C by step 3.
(iii) Let K′ ⊆ A be compact and δ > 0. K′ is bounded, so by step 6 there is k ≥ 1 with η_k(x) ≤ δ for all x ∈ K′. Let x ∈ K′ and y ∈ A with |x − y| < 1/k. If y = x, then |g(y) − g(x) − Dg(x)(y − x)| = 0 ≤ δ|y − x|. If y ≠ x, then y ∈ C and 0 < |y − x| < 1/k, so |g(y) − g(x) − Dg(x)(y − x)| = |R(x,y)| |y − x| ≤ η_k(x)|y − x| ≤ δ|y − x|.
Hence for every compact K′ ⊆ A and δ > 0 there is ρ := 1/k > 0 such that |g(y) − g(x) − Dg(x)(y − x)| ≤ δ|y − x| for all x ∈ K′ and y ∈ A with |x − y| < ρ. This is Simon's condition 1.6 (‡) for h := g|A and τ := Dg|A. It is exactly SimonGMT's HasWhitneyC1Compatibility A g (fderiv ℝ g), with fields continuous_value, continuous_derivative and remainder.

8. (Whitney extension and conclusion.)
- By the Whitney Extension Theorem (Simon Ch. 2, Theorem 1.6; see [EG92, §6.5], [Fed69, 3.1.14]) there is a C¹ function h : ℝⁿ → ℝ with h(a) = g(a) and HasFDerivAt h (Dg(a)) a for every a ∈ A.
- In Lean this is SimonGMT Poincare.SimonGMT.Chapter02.exists_contDiff_one_extension_of_whitney : IsClosed A → HasWhitneyC1Compatibility A h D → ∃ g′, ContDiff ℝ 1 g′ ∧ EqOn g′ h A ∧ ∀ a ∈ A, HasFDerivAt g′ (D a) a, in Poincare/SimonGMT/Chapter02/WhitneyExtension.lean of the pinned simongmt package.
- That module has no prebuilt .olean in the shared package tree, so it cannot be imported directly. Its source compiles unchanged, using only propext, Classical.choice and Quot.sound, when copied into a new file under GMT/Ch06/ that imports GMT.Ch06.Submission, Poincare.SimonGMT.Chapter02.WhitneyJet and Poincare.SimonGMT.Chapter02.WhitneyPartition (both built).
- Let x ∈ A. Then g(x) = h(x). By uniqueness of the Fréchet derivative, fderiv ℝ h x = Dg(x).
- Since x ∈ A ⊆ D, g is differentiable at x, i.e. HasFDerivAt g (Dg(x)) x, which is HasFDerivAt g (fderiv ℝ h x) x.
- Together with step 6 (A is closed and Lⁿ(ℝⁿ ∖ A) < ε), this proves the theorem. ∎

## Key steps

1. Reduce to 0 < ε ≤ 1. Cover ℝⁿ, up to the null set of spheres |x| = j, by bounded open annuli S_j; unions of closed F_j ⊆ S_j are closed, and continuity on each F_j glues (★).
2. Rademacher: g is differentiable on a Borel set D of full measure; Dg = fderiv ℝ g is Borel measurable with ‖Dg‖ ≤ K on D.
3. Lusin on each finite-measure set S_j ∩ D (coordinatewise) plus closed inner regularity, glued by (★): a closed C ⊆ D with Dg continuous on C and Lⁿ(ℝⁿ ∖ C) ≤ ε/4.
4. η_k(x) := sup{|R(x,y)| : y ∈ C, 0 < |y − x| < 1/k} is bounded by 2K, decreases to 0 on C, and is Borel (lower semicontinuous on C).
5. Egoroff on each C_j = C ∩ S_j gives A₀ ⊆ C with Lⁿ(C ∖ A₀) ≤ ε/8 and η_k → 0 uniformly on each C_j ∖ T_j.
6. Closed A_j ⊆ C_j ∖ T_j by inner regularity. A := ⋃ A_j is closed, Lⁿ(ℝⁿ ∖ A) ≤ ε/2 < ε, and η_k → 0 uniformly on bounded subsets of A.
7. For compact K′ ⊆ A: |g(y) − g(x) − Dg(x)(y − x)| ≤ η_k(x)|y − x| for x ∈ K′, y ∈ A, |x − y| < 1/k. This is Whitney's (‡), i.e. HasWhitneyC1Compatibility A g Dg.
8. Whitney extension (SimonGMT exists_contDiff_one_extension_of_whitney, vendored) gives a C¹ h with h = g and HasFDerivAt h (Dg a) a on A. Uniqueness gives fderiv h = Dg on A, and A ⊆ D gives HasFDerivAt g (fderiv ℝ h x) x.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project, project_commit d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD in lake-packages-25730c7c/{simongmt,mathlib} = 2b3663083f3fe399b6296fb8eaee52169170e197, 25730c7c759d108ef87ab70af2342a196760f79d`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean vs workspace GMT/Ch06/Contract.lean (identical); diff workspace Contract.lean Submission.lean (identical)`
- `python3 over dag.json: lean_name of all 90 nodes; keyword scan Whitney|Lusin|Egoroff|Egorov|Rademacher|C¹ approx|antilipschitz; assert frozen parent lean_statement byte-equal to the selected type`
- `sed -n 155,275p book/chapter-02.txt (Simon Thm 1.5, Thm 1.6 (‡), Remark 1.7, printed proof of 1.5)`
- `grep -rn 'rademacher|approximation theorem|Theorem 1.5|c1_approx|exists_contDiff_one' simongmt/Poincare/SimonGMT --include=*.lean`
- `ls simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter0{1,2,3} | grep olean`
- `sed -n 1,388p Chapter02/WhitneyExtension.lean; sed -n 1,227p Chapter02/WhitneyJet.lean; grep -n theorem Chapter01/Lusin.lean Chapter02/Lipschitz.lean`
- `rg -n -i lusin mathlib/Mathlib`
- `rg -n 'extend_finite_dimension|exists_antilipschitzWith|isOpen_injective|approximates_deriv_on_nhds|antilipschitzWith|exists_isClosed_sdiff_lt|exists_isClosed_lt_add|tendstoUniformlyOn_of_ae_tendsto|measurable_fderiv|measurableSet_of_differentiableAt|extend_pi|extend_real' on the snapshot mathlib/Mathlib; grep addHaar_sphere_of_ne_zero, LocallyFinite.isClosed_iUnion, LipschitzWith.ae_differentiableAt in lake-packages mathlib (same commit)`
- `python3 -I scope.py: contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py; python3 -I validate.py: lean_contract.validate_lean_statement on the 4 child statements`
- `lake env lean GMT/Ch06/Submission.lean -o .lake/build/lib/lean/GMT/Ch06/Submission.olean (scratch project, packages symlinked; find -newer confirms shared tree untouched)`
- `lake env lean Scratch/{WhitneyExtCopy,WhitneyVendored,Names,Names2,Names3,Stmts,Assembly,Vec,Small,Combined}.lean with #check and #print axioms`
- `WebSearch (standard): Evans–Gariepy Whitney extension / C¹ approximation theorem numbering (not confirmed; cite by section only)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/LocallyFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/tmp/c1pieces_scratch/Scratch/scope_prefix.txt`
- `/tmp/c1pieces_scratch/Scratch/Stmts.lean`
- `/tmp/c1pieces_scratch/Scratch/Assembly.lean`
- `/tmp/c1pieces_scratch/Scratch/Vec.lean`
- `/tmp/c1pieces_scratch/Scratch/Small.lean`
- `/tmp/c1pieces_scratch/Scratch/Combined.lean`
- `/tmp/c1pieces_scratch/Scratch/WhitneyExtCopy.lean`
- `/tmp/c1pieces_scratch/Scratch/WhitneyVendored.lean`
- `/tmp/c1pieces_scratch/Scratch/Names.lean`
- `/tmp/c1pieces_scratch/Scratch/Names2.lean`
- `/tmp/c1pieces_scratch/Scratch/Names3.lean`
- `/tmp/c1pieces_tools/stmts.json`
- `/tmp/c1pieces_tools/gen_combined.py`

The snapshot (project d8d46c95, Mathlib 25730c7c, simongmt 2b36630) holds the frozen Ch06 Contract, byte-identical to the workspace Contract and Submission. Only the 90 existing node names are reserved in dag.json, and no node states a Whitney or C¹-approximation theorem, so lpf_c1_approximation_real, lpf_c1_approximation_eucl, lpf_c1_local_antilipschitz and lpf_lipschitz_localization are free.

Simon Ch. 2, pp. 42–44 gives Thm 1.5 and its printed proof (Rademacher, Lusin for infinite measure, η_k, Egoroff on C ∩ B_j(0), closed A ⊆ A₀) and Whitney's Thm 1.6 with condition (‡).

SimonGMT provides:
- a complete Whitney C¹ extension theorem, Chapter02.exists_contDiff_one_extension_of_whitney, with hypothesis HasWhitneyC1Compatibility (continuity on A plus a remainder bound for x ∈ compact K ⊆ A, y ∈ A); WhitneyExtension.olean is absent, but the source compiles unchanged next to import GMT.Ch06.Submission with only propext, Classical.choice and Quot.sound, so it can be vendored under GMT/Ch06/;
- Lusin, Chapter01.exists_isClosed_continuousOn_of_measurable (built; importable with standard axioms);
- Rademacher.
SimonGMT has no packaged C¹ approximation theorem.

The Mathlib snapshot has no Lusin theorem for measurable functions (only Lusin–Souslin and Lusin separation). It does provide: Egorov (tendstoUniformlyOn_of_ae_tendsto), closed inner regularity (MeasurableSet.exists_isClosed_sdiff_lt), measurable_fderiv, measurableSet_of_differentiableAt, LipschitzWith.ae_differentiableAt, addHaar_sphere_of_ne_zero, LocallyFinite.isClosed_iUnion, LipschitzOnWith.extend_finite_dimension, LinearMap.exists_antilipschitzWith, HasStrictFDerivAt.approximates_deriv_on_nhds, ContinuousLinearMap.isOpen_injective, disjointed, iUnion_disjointed and TopologicalSpace.exists_countable_basis.

All four child statements elaborate in the exact comparator child scope and pass validate_lean_statement. Scratch/Combined.lean kernel-checks the vector child from the scalar child, both small lemmas outright, and the frozen parent type from the children. Its comparator-style target uses standard axioms plus sorryAx from the scalar C¹ approximation child only.
