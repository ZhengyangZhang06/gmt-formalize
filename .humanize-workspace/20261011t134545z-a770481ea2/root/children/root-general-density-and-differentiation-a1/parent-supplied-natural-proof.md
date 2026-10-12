# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.general_density_and_differentiation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

PROOF OF `GeneralDensityTheorem.{u} ∧ LebesgueDifferentiation.{u}` (Simon, Ch. 1, Remark 3.11(1), Theorems 3.13, 3.15, 3.16 and Corollary 3.17; printed proofs, transcribed and completed).

Statements. Let (X, d) be a metric space and μ an outer measure on X which is Borel regular, open σ-finite (X = ⋃_j V_j, V_j open, μ(V_j) < ∞) and has the Symmetric Vitali Property (SVP; Def. 3.10 as formalized: for every A ⊆ X with μ(A) < ∞ and every set 𝓑 of pairs (x, r) with x ∈ A, r > 0, which is fine on A — for all x ∈ A and ε > 0 there is r ∈ (0, ε) with (x, r) ∈ 𝓑 — there is a countable 𝓑' ⊆ 𝓑 whose closed balls B_r(x) are pairwise disjoint and μ(A ∖ ⋃_{(x,r)∈𝓑'} B_r(x)) = 0).
 (3.16) If A is μ-measurable, then q_x(ρ) := μ(A ∩ B_ρ(x))/μ(B_ρ(x)) → 1 as ρ ↓ 0 for μ-a.e. x ∈ A, and q_x(ρ) → 0 for μ-a.e. x ∈ X ∖ A.
 (3.17) If f : X → ℝ is μ-measurable and every x has some ρ_x > 0 with ∫_{B_{ρ_x}(x)} |f| dμ < ∞, then for μ-a.e. x, (μ(B_ρ(x)))^{−1} ∫_{B_ρ(x)} f dμ → f(x) as ρ ↓ 0.

Conventions. Quotients of values in [0, ∞] use the conventions of [0, ∞]: a/0 = ∞ for a > 0, 0/0 = 0, a/∞ = 0 for a < ∞ (Lean `ENNReal`); at all points that matter below the denominators are in (0, ∞). Integrals are with respect to μ on the σ-algebra M_μ of μ-measurable sets (Lemma 1.6/Remark 1.7; Lean `caratheodoryMeasure μ`); “μ-measurable function” means M_μ-measurable. “P for μ-a.e. x ∈ E” means μ({x ∈ E : not P(x)}) = 0. In the formal statement of 3.17 the average is written (μ(B_ρ(x))).toReal⁻¹ · ∫_{B_ρ(x)} f dμ (Bochner integral); at the points and radii used below 0 < μ(B_ρ(x)) < ∞ and f is integrable on B_ρ(x), so this is the usual average. Standard facts: M_μ is a σ-algebra containing all μ-null sets, μ is countably additive on it; a countable union of null sets is null.

Dependency. Theorem 1.15 = sibling `borel_regular_approximation` (used for finite Borel regular measures; in a metric space every closed set C ≠ ∅ equals ⋂_k {dist(·, C) < 1/k}, a countable intersection of open sets).

STEP 1 (restriction lemma; remarks after (1.12)). Let σ be a Borel regular outer measure and Y ⊆ X either Borel, or σ-measurable with σ(Y) < ∞. Then σ⌞Y (S ↦ σ(Y ∩ S)) is Borel regular, and every σ-measurable set is σ⌞Y-measurable.
 Proof. For E σ-measurable: σ⌞Y(S) = σ(S∩Y∩E) + σ((S∩Y)∖E) = σ⌞Y(S∩E) + σ⌞Y(S∖E); so Borel sets are σ⌞Y-measurable. Borel hulls, Y Borel: for S take Borel B₃ ⊇ S ∩ Y with σ(B₃) = σ(S ∩ Y); B := B₃ ∪ (X ∖ Y) is Borel, contains S, and σ⌞Y(B) ≤ σ(B₃) = σ⌞Y(S). Y measurable with σ(Y) < ∞: take Borel B₁ ⊇ Y with σ(B₁) = σ(Y), so σ(B₁ ∖ Y) = 0, and Borel B₂ ⊇ B₁ ∖ Y with σ(B₂) = 0; then B := B₃ ∪ (X ∖ B₁) ∪ B₂ ⊇ S is Borel and σ⌞Y(B) ≤ σ(B₃) + σ(Y ∖ B₁) + σ(B₂) = σ⌞Y(S).

STEP 2 (localization to finite measures). For each j let μ_j := μ⌞V_j. Then μ_j is Borel regular (Step 1, V_j open), finite (μ_j(X) = μ(V_j) < ∞), and has the SVP: if μ_j(A) = μ(A ∩ V_j) < ∞ and 𝓑 is fine on A, then the pairs of 𝓑 centred in A ∩ V_j form a family fine on A ∩ V_j, and the SVP of μ yields a countable disjoint 𝓑' with μ((A ∩ V_j) ∖ ⋃𝓑') = 0, i.e. μ_j(A ∖ ⋃𝓑') = 0. Every μ-measurable set is μ_j-measurable (Step 1). For x ∈ V_j there is ρ_x' > 0 with B_ρ(x) ⊆ V_j for ρ < ρ_x' (V_j open), and then μ_j(E ∩ B_ρ(x)) = μ(E ∩ B_ρ(x)) for every E ⊆ X. A set N ⊆ V_j is μ-null iff it is μ_j-null. Hence, if a pointwise property of x is determined by the values μ(E ∩ B_ρ(x)) (finitely many fixed E) for arbitrarily small ρ, and it holds μ_j-a.e. for μ_j, then it holds for μ-a.e. x ∈ V_j; as X = ⋃_j V_j, it then holds μ-a.e. on X.

In Steps 3–6, μ and ν denote Borel regular outer measures with μ(X), ν(X) < ∞, μ has the SVP, and U₀ := {x : μ(B_ρ(x)) = 0 for some ρ > 0}.

STEP 3 (Remark 3.11(1)). μ(U₀) = 0. The family {(x, ρ) : x ∈ U₀, ρ > 0, μ(B_ρ(x)) = 0} is fine on U₀ (if μ(B_R(x)) = 0 then μ(B_ρ(x)) = 0 for all ρ ≤ R). By the SVP (μ(U₀) < ∞) there is a countable disjoint subfamily 𝓑' with μ(U₀ ∖ ⋃𝓑') = 0, and μ(⋃𝓑') ≤ Σ_{𝓑'} μ(B) = 0. Hence μ(U₀) = 0. For x ∉ U₀: 0 < μ(B_ρ(x)) < ∞ for every ρ > 0.

STEP 4 (Theorem 3.13, comparison, finite case). Let A ⊆ X and t > 0 with limsup_{ρ↓0} ν(B_ρ(x))/μ(B_ρ(x)) ≥ t for every x ∈ A ∖ U₀. Then ν(A) ≥ t·μ(A).
 Proof (printed). μ(A) = μ(A ∖ U₀) by Step 3. Let τ ∈ (0, t) and U ⊇ A open. Let 𝓑 := {(x, ρ) : x ∈ A ∖ U₀, ρ > 0, B_ρ(x) ⊆ U, ν(B_ρ(x)) > τ μ(B_ρ(x))}. 𝓑 is fine on A ∖ U₀: for such x the quotient exceeds τ for arbitrarily small ρ (its limsup is ≥ t > τ), B_ρ(x) ⊆ U for small ρ, and as μ(B_ρ(x)) ∈ (0, ∞) the quotient exceeds τ iff ν(B_ρ(x)) > τμ(B_ρ(x)). By the SVP (μ(A ∖ U₀) < ∞) there are countably many disjoint B_j ∈ 𝓑 with μ((A ∖ U₀) ∖ ⋃_j B_j) = 0. Closed balls are ν-measurable, so
  τμ(A) = τμ(A ∖ U₀) ≤ τ Σ_j μ(B_j) ≤ Σ_j ν(B_j) = ν(⋃_j B_j) ≤ ν(U).
 By Theorem 1.15(1) (sibling) for ν (Borel regular, finite, hence open σ-finite with V_n = X), inf_{U⊇A open} ν(U) = ν(A); so τμ(A) ≤ ν(A), and τ ↑ t gives the claim.

STEP 5 (Theorem 3.15, general upper density theorem, finite case; “the proof is essentially the same as the proof of 3.6 with 3.13 in place of 3.3”, details supplied). Let E ⊆ X be ν-measurable. Then for μ-a.e. x ∈ X ∖ E: ν(E ∩ B_ρ(x))/μ(B_ρ(x)) → 0 as ρ ↓ 0.
 Proof. For t > 0 let S_t := {x ∈ X ∖ (E ∪ U₀) : limsup_{ρ↓0} ν(E ∩ B_ρ(x))/μ(B_ρ(x)) ≥ t}. Let C ⊆ E be closed and ν_C := ν⌞(E ∖ C), Borel regular and finite by Step 1 (E ∖ C is ν-measurable). For x ∈ S_t we have x ∉ C, so B_ρ(x) ∩ C = ∅ for small ρ and ν_C(B_ρ(x)) = ν((E ∖ C) ∩ B_ρ(x)) = ν(E ∩ B_ρ(x)); hence limsup ν_C(B_ρ(x))/μ(B_ρ(x)) ≥ t on S_t = S_t ∖ U₀. Step 4 with ν_C in place of ν gives t·μ(S_t) ≤ ν_C(S_t) ≤ ν(E ∖ C). By Theorem 1.15(2) (sibling) for ν⌞E (Borel regular, finite; E is ν⌞E-measurable) there are closed C_k ⊆ E with ν(C_k) → ν(E), so ν(E ∖ C_k) = ν(E) − ν(C_k) → 0. Thus μ(S_t) = 0. For x ∈ X ∖ (E ∪ U₀ ∪ ⋃_m S_{1/m}) the limsup is 0, so the nonnegative quotient tends to 0; the excluded set is μ-null (Step 3).

STEP 6 (Theorem 3.16, finite case). Let A be μ-measurable. For x ∉ U₀ and ρ > 0, since 0 < μ(B_ρ(x)) < ∞ and A is μ-measurable,
  μ(A ∩ B_ρ(x))/μ(B_ρ(x)) + μ(B_ρ(x) ∖ A)/μ(B_ρ(x)) = 1.
By Step 5 with ν := μ and E := A, the first term → 0 for μ-a.e. x ∈ X ∖ A. By Step 5 with ν := μ and E := X ∖ A, the second term → 0, hence the first → 1, for μ-a.e. x ∈ A.

STEP 7 (Theorem 3.16, general; printed “we can assume without loss of generality that μ(X) < ∞”). Let A be μ-measurable. For each j, A is μ_j-measurable and Step 6 for μ_j gives: for μ_j-a.e. x, μ_j(A ∩ B_ρ(x))/μ_j(B_ρ(x)) tends to 1 if x ∈ A and to 0 if x ∉ A. For x ∈ V_j this quotient equals q_x(ρ) for ρ < ρ_x' (Step 2). Hence q_x(ρ) → 1 for μ-a.e. x ∈ A ∩ V_j and q_x(ρ) → 0 for μ-a.e. x ∈ V_j ∖ A; taking the union over j proves both clauses of `GeneralDensityTheorem`.

STEP 8 (Borel envelopes, finite case). If σ is Borel regular with σ(X) < ∞ and E is σ-measurable, there is a Borel F ⊇ E with σ(F ∖ E) = 0 (a Borel hull F with σ(F) = σ(E), then σ(F ∖ E) = σ(F) − σ(E) = 0).

STEP 9 (Corollary 3.17 for nonnegative integrable f, finite μ). Assume (as in Steps 3–6) μ finite with the SVP and let f : X → [0, ∞) be μ-measurable with ∫_X f dμ < ∞. Then for μ-a.e. x, avg_ρ(x) := μ(B_ρ(x))^{−1}∫_{B_ρ(x)} f dμ → f(x).
 9.1 (printed: “let ν₀(A) = ∫_A f dμ for each Borel set A and let ν be the associated Borel regular outer measure as in Remark 1.11”). Put ν(S) := inf{∫_F f dμ : F ⊇ S Borel}. By Remark 1.11, ν is a Borel regular outer measure with ν(F) = ∫_F f dμ for Borel F, and ν(X) = ∫ f dμ < ∞. [Proof of Remark 1.11 here: countable subadditivity follows from countable additivity of F ↦ ∫_F f dμ applied to Borel covers; the infimum is attained (intersect a minimizing sequence of Borel sets); a Borel G is ν-measurable: for S with ν(S) < ∞ choose Borel C ⊇ S with ν(C) = ν(S), then ν(S ∩ G) + ν(S ∖ G) ≤ ∫_{C∩G} f dμ + ∫_{C∖G} f dμ = ∫_C f dμ = ν(S).]
 9.2 Every μ-null set N is ν-null (a Borel G ⊇ N with μ(G) = 0 gives ν(N) ≤ ∫_G f dμ = 0). For μ-measurable E: by Step 8 there is a Borel F ⊇ E with μ(F ∖ E) = 0, so ∫_F f dμ = ∫_E f dμ, while every Borel F' ⊇ E has ∫_{F'} f dμ ≥ ∫_E f dμ; hence ν(E) = ∫_E f dμ. Moreover E = F ∖ (F ∖ E) with F Borel and F ∖ E ν-null, so E is ν-measurable.
 9.3 (printed (*)) For i, j ≥ 1 let A_ij := {x : (j−1)/i ≤ f(x) < j/i} (μ-measurable); for each i, X is the disjoint union of the A_ij, j ≥ 1. For x ∉ U₀, ρ > 0 and B := B_ρ(x), using 9.2:
  ((j−1)/i)·μ(B ∩ A_ij) ≤ ∫_{B∩A_ij} f dμ ≤ ∫_B f dμ = ν(B ∩ A_ij) + ν(B ∖ A_ij) ≤ (j/i)·μ(B ∩ A_ij) + ν(B ∖ A_ij).
 By Step 6, μ(B_ρ(x) ∩ A_ij)/μ(B_ρ(x)) → 1 for μ-a.e. x ∈ A_ij. By Step 5 applied to the pair (ν, μ) (ν finite Borel regular by 9.1) and the ν-measurable set E := X ∖ A_ij (9.2), ν(B_ρ(x) ∖ A_ij)/μ(B_ρ(x)) → 0 for μ-a.e. x ∈ A_ij. Dividing by μ(B_ρ(x)) ∈ (0, ∞): for μ-a.e. x ∈ A_ij,
  (j−1)/i ≤ liminf_{ρ↓0} avg_ρ(x) ≤ limsup_{ρ↓0} avg_ρ(x) ≤ j/i,
 and since (j−1)/i ≤ f(x) < j/i on A_ij, f(x) − 1/i ≤ liminf avg ≤ limsup avg ≤ f(x) + 1/i. Removing the countably many exceptional null sets (all i, j, and U₀), for μ-a.e. x this holds for every i, so avg_ρ(x) → f(x).

STEP 10 (integrable signed f, finite μ; printed “since f = max{f,0} − max{−f,0} we can assume f ≥ 0”). If f is μ-measurable with ∫|f| dμ < ∞, apply Step 9 to f⁺ := max{f, 0} and f⁻ := max{−f, 0}; averages are linear, so avg_ρ(f)(x) = avg_ρ(f⁺)(x) − avg_ρ(f⁻)(x) → f⁺(x) − f⁻(x) = f(x) for μ-a.e. x (finite limits).

STEP 11 (localization for the general μ; supplies the reduction “we can assume μ(X) < ∞” when f is only locally integrable). Let f be as in (3.17). Fix j and let 𝓑_j := {(c, r) : c ∈ V_j, r > 0, B_{2r}(c) ⊆ V_j, ∫_{B_{2r}(c)} |f| dμ < ∞}. It is fine on V_j: for c ∈ V_j and ε > 0 choose r < ε with 2r ≤ ρ_c and B_{2r}(c) ⊆ V_j. By the SVP of μ (μ(V_j) < ∞) there is a countable disjoint 𝓓_j ⊆ 𝓑_j with μ(V_j ∖ ⋃_{(c,r)∈𝓓_j} B_r(c)) = 0. For b = (c, r) ∈ 𝓓_j let f_b := f·1_{B_{2r}(c)}; it is μ_j-measurable (μ-measurable sets are μ_j-measurable, Step 1), and since μ_j and μ agree on μ-measurable subsets of V_j, ∫_E g dμ_j = ∫_E g dμ for every μ-measurable g and every μ-measurable E ⊆ V_j (whenever either side is defined); in particular ∫|f_b| dμ_j = ∫_{B_{2r}(c)} |f| dμ < ∞. Step 10 for the finite measure μ_j (Borel regular with the SVP, Step 2) and f_b gives: for μ_j-a.e. x, μ_j(B_ρ(x))^{−1}∫_{B_ρ(x)} f_b dμ_j → f_b(x). If x lies in the open ball U_{2r}(c) and ρ < 2r − d(x, c), then B_ρ(x) ⊆ B_{2r}(c) ⊆ V_j, so μ_j(B_ρ(x)) = μ(B_ρ(x)), ∫_{B_ρ(x)} f_b dμ_j = ∫_{B_ρ(x)} f dμ and f_b(x) = f(x). Hence avg_ρ(x) → f(x) for μ-a.e. x ∈ U_{2r}(c) ⊇ B_r(c). Taking the union over the countably many j and b ∈ 𝓓_j, the convergence holds for μ-a.e. x ∈ ⋃_j ⋃_{(c,r)∈𝓓_j} B_r(c), which contains μ-almost every point of X (each V_j ∖ ⋃_{𝓓_j} B_r(c) is null and ⋃_j V_j = X).

STEP 12 (formal conclusion of 3.17). U₀(μ) := {x : μ(B_ρ(x)) = 0 for some ρ > 0} is μ-null: U₀(μ) ∩ V_j ⊆ U₀(μ_j) and μ(U₀(μ) ∩ V_j) = μ_j(U₀(μ) ∩ V_j) ≤ μ_j(U₀(μ_j)) = 0 by Step 3. For x ∉ U₀(μ), x ∈ V_j, and 0 < ρ < min(ρ_x', ρ_x): 0 < μ(B_ρ(x)) < ∞, so (μ(B_ρ(x))).toReal⁻¹ = 1/μ(B_ρ(x)), and f is integrable on B_ρ(x), so ∫_{B_ρ(x)} f dμ is the Lebesgue integral. Thus the expression in `LebesgueDifferentiation` equals avg_ρ(x) for all small ρ, and Step 11 proves it tends to f(x) for μ-a.e. x. (The formal hypotheses “Measurable[μ.caratheodory] f” and “∫⁻_{B_ρ(x)} ofReal|f| d(caratheodoryMeasure μ) < ∞” are exactly μ-measurability of f and ∫_{B_ρ(x)} |f| dμ < ∞.) Together with Step 7 this proves the conjunction. ∎

Formalization note (non-binding): `Poincare.SimonGMT.Chapter01.simon_theorem_3_16` (Chapter01/GeneralDensity.lean: a.e. with respect to `hμ.toBorelMeasure`, limit `A.indicator 1 x`; null sets agree with μ's by `toBorelMeasure_apply_all`) and `simon_corollary_3_17_of_caratheodory` (Chapter01/GeneralDifferentiation.lean: same hypotheses, integrals against `hμ.toBorelMeasure`). To transport integrals: `(caratheodoryMeasure μ).trim hμ.borel_le_caratheodory = hμ.toBorelMeasure` (both agree on Borel sets), `f` is a.e. Borel by `IsBorelRegularOuterMeasure.aemeasurable_of_caratheodory`, then `setLIntegral_trim_ae`, `restrict_trim`, `integral_trim_ae`. The frozen statement fixes one universe `u` for both conjuncts.

## Key steps

1. Restriction lemma and localization to the finite measures μ⌞V_j, which remain Borel regular with the Symmetric Vitali Property.
2. Remark 3.11(1): the zero-ball set U₀ is μ-null, by the Symmetric Vitali Property.
3. Theorem 3.13 (finite case): an upper density ≥ t on A gives ν(A) ≥ t·μ(A), via the Vitali property and outer regularity (Theorem 1.15(1)).
4. Theorem 3.15 (finite case): the density of ν⌞E with respect to μ vanishes μ-a.e. off E, via 3.13 and closed inner approximation (Theorem 1.15(2)).
5. Theorem 3.16: the two complementary quotients sum to 1; apply 3.15 to A and to X ∖ A, then transfer from μ⌞V_j to μ.
6. Corollary 3.17 for integrable f ≥ 0 and finite μ: ν = f dμ (Remark 1.11); level sets A_ij, 3.16 and 3.15 squeeze the averages within 1/i of f(x).
7. Signed and locally integrable f: split f = f⁺ − f⁻, and localize by a Vitali-selected countable family of balls on whose doubles f is integrable.
8. Formal conventions: for μ-a.e. x and small ρ, 0 < μ(B_ρ(x)) < ∞ and f is integrable on B_ρ(x), so toReal⁻¹·∫ is the average.

## Reference use

### local-project

Queries:
- `cat manifest.json (snapshot root e8e26216f05cbb4e)`
- `rg -n '^def (CaratheodoryCriterion|BorelRegularApproximation|LusinTheorem|LebesgueEqHausdorff|IsodiametricInequality|UpperDensityComparison|UpperDensityTheorem|BesicovitchCovering|GeneralDensityTheorem|LebesgueDifferentiation|RadonNikodymTheorem|HausdorffDensityBounds|RieszPositive|RieszVector|RadonCompactness)|^theorem main_theorem|^universe|^open|^namespace' project/GMT/Ch01/Contract.lean`
- `cmp project/GMT/Ch01/Contract.lean project/GMT/Ch01/Submission.lean`
- `rg -n -c Poincare.SimonGMT project mathlib/Mathlib`
- `rg -n 'theorem simon_theorem' . (no match: SimonGMT is not in the snapshot)`
- `rg -n 'theorem borel_le_caratheodory|def IsMetric' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n '^theorem exist_disjoint_covering_families|^theorem isEmpty_satelliteConfig_multiplicity|def multiplicity' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `rg -n 'theorem integral_rieszMeasure|instance rieszMeasure_regular|instance regular_rieszMeasure' mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/NNReal.lean mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `rg -n 'theorem volume_ball|theorem volume_closedBall' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `rg -n 'def IsCaratheodory|def caratheodory |theorem isCaratheodory_iff' mathlib/Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean`
- `rg -n 'theorem toMeasure_apply|theorem le_toMeasure_apply' mathlib/Mathlib/MeasureTheory/Measure/OuterMeasure.lean; rg -n 'theorem ae_iff' mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `rg -n 'theorem setLIntegral_trim_ae|theorem lintegral_trim_ae' mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean; rg -n 'theorem integral_trim_ae|theorem integral_trim ' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean; rg -n 'theorem restrict_trim' mathlib/Mathlib/MeasureTheory/Measure/Trim.lean`
- `rg -n 'sigmaCompactSpace_of_locallyCompact_secondCountable|noncomputable def choice|theorem exists_superset_of_isCompact' mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `rg -n '^instance|^theorem' mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean; rg -n 'metrizableSpace_of_t3_secondCountable' mathlib/Mathlib/Topology/Metrizable/Urysohn.lean; rg -n 'theorem exists_compact_superset' mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `rg -n 'theorem exists_continuous_one_zero_of_isCompact' mathlib/Mathlib/Topology/UrysohnsLemma.lean; rg -n 'theorem IsCompact.tendsto_subseq' mathlib/Mathlib/Topology/Sequences.lean`
- `rg -n 'theorem tendsto_iff_forall_integral_tendsto' mathlib/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean; rg -n -F 'CompactSpace (ProbabilityMeasure' mathlib/Mathlib/MeasureTheory/Measure/Prokhorov.lean; rg -n 'theorem measure_iUnion_le|theorem measure_mono_null' mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `test -f on every cited snapshot file (all present); cmp of cited Mathlib files against lake-packages-25730c7c/mathlib (identical)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/GMT/Ch01/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/GMT/Ch01/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/GMT/Ch01/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/PROBLEM.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/lakefile.toml`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/OuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/Trim.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Metrizable/Urysohn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/Prokhorov.lean`

The manifest pins project ec1c322 and Mathlib 25730c7c. In the snapshot, project/GMT/Ch01/Contract.lean is byte-identical to Submission.lean. It defines exactly the fifteen Props CaratheodoryCriterion … RadonCompactness (lines 88–303), with main_theorem at line 313, inside namespace GMT.Ch01 with `universe u v` (line 69) and the opens at lines 63–65. Each child lean_statement is one of these Props or a conjunction of two of them; the two merged children with universe parameters share the declared universe u, which the comparator replays from that scope. README.md maps the conjuncts to SimonGMT theorems and documents the 4.16 erratum (second countability). That erratum is applied in radon_compactness. The snapshot contains no SimonGMT declarations: rg finds 'Poincare.SimonGMT' only as imports and opens in the project files, and 'theorem simon_theorem' has no match. The package is pinned in project/lake-manifest.json and lives outside the snapshot, so the children cite it only in non-binding formalization notes. The snapshot's Mathlib contains the facts those notes rely on:
- OuterMeasure.IsMetric and borel_le_caratheodory: Measure/Hausdorff.lean:137,161.
- Besicovitch.exist_disjoint_covering_families (Covering/Besicovitch.lean:455), multiplicity and isEmpty_satelliteConfig_multiplicity (BesicovitchVectorSpace.lean:98,488).
- NNRealRMK.integral_rieszMeasure and rieszMeasure_regular (RieszMarkovKakutani/NNReal.lean:47,66); the real RMK (Real.lean:345,357).
- EuclideanSpace.volume_ball and volume_closedBall: Lebesgue/VolumeOfBalls.lean:307,324.
- IsCaratheodory and the caratheodory σ-algebra: OuterMeasure/Caratheodory.lean:55,176,181.
- toMeasure_apply and le_toMeasure_apply (Measure/OuterMeasure.lean:46,50); ae_iff (OuterMeasure/AE.lean:134).
- setLIntegral_trim_ae (Integral/Lebesgue/Add.lean:490); integral_trim and integral_trim_ae (Bochner/Basic.lean:1301,1332); restrict_trim (Measure/Trim.lean:108).
- σ-compactness and compact exhaustions: SigmaCompact.lean:187,376,418.
- Urysohn's lemma: UrysohnsLemma.lean:404.
- Separability of C(X,Y): ContinuousMap/SecondCountableSpace.lean:108. Metrizability: Metrizable/Urysohn.lean:127.
- Compact supersets: LocallyCompact.lean:58. IsCompact.tendsto_subseq: Sequences.lean:298.
- Weak convergence and Prokhorov: FiniteMeasure.lean:727; Prokhorov.lean:176.
The cited Mathlib files are byte-identical to the packages used by the build. The mathematical arguments of the children are the printed proofs of the source and do not depend on these declarations.
