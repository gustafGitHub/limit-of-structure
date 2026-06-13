/-
================================================================================
  Where Structure Ends — Lean 4 formalization (machine-checked core)
  Companion to: G. Ullman, "Where Structure Ends" (2026).
  Article version DOI: 10.5281/zenodo.20666955   Concept DOI: 10.5281/zenodo.17159948
================================================================================

  WHAT THIS FILE FORMALIZES
  -------------------------
  The paper's formal core is a single engine — *fiber-blindness of descent* —
  applied in four registers:

    1.  The Quotient Test (§3 of the paper) as a genuine factorization theorem:
        a quantity is invariant under admissible transformations IFF it
        descends to the structural quotient, and the descent is UNIQUE.
    2.  The structural dilemma (§7): a quantity that separates two perspectives
        in a common fiber cannot be invariant, hence cannot be an objective
        descended observable relative to that quotient.
    3.  The toy collapse endpoint (§6), its signature-factorization
        no-representation corollary, and the time-degeneration corollary
        discussed in paper §6.
    4.  Non-structural facts under forgetfulness (§4) and conditional
        metaphysical corollaries about phenomenal character and the Prop-valued
        phenomenality special case (§5).

  SCOPE OF THE FORMALIZATION
  --------------------------
  This file works at the quotient/setoid level: admissible transformations are
  the equivalence relation `≈` and descent is the universal property of the
  quotient. The genuine group-action case (§2') is recovered as the orbit
  relation `orbitRel G Obs`. The paper's broader categorical / groupoidal
  language is represented here only by the induced equivalence relation on
  perspectives; a full `CategoryTheory.Groupoid` treatment is deliberately out
  of scope. Likewise the degeneration `Collapses` (§6 of the paper) is a toy *endpoint*
  condition (globally constant invariant signature), NOT the full order-
  theoretic `S_min` of §6. Future refinements would add the missing order-
  theoretic structure explicitly.

  WHAT IS *NOT* A THEOREM (and must not be coded as one)
  ------------------------------------------------------
  Primitivism about phenomenality and the Ontological Closure Principle are
  the paper's METAPHYSICAL PREMISES (the paper itself says "a metaphysical
  stance, not a theorem"). They live in `namespace OE.Metaphysics` as explicit
  hypotheses / definitions, NEVER as global `axiom`s. The verified core
  therefore stays free of extra-logical commitments. The file also does not
  formalize IIT, the unfolding argument, the Kleiner--Hoel substitution
  argument, Chalmers' structure-and-dynamics argument, the Newman problem,
  Global Workspace Theory, or actual AI architectures; the paper treats these
  only as schematic applications of the quotient pattern.

  Axiom profile to audit
  (see the audit block at the end of the file): the core descent/no-go theorems
  should return only `[Quot.sound]`, and several should be fully axiom-free;
  the classical corollaries and the group realization should carry
  `[propext, Classical.choice, Quot.sound]` (classicality entering via
  `by_cases`/`by_contra`); the collapse no-representation theorem
  `no_factor_through_collapsed_signature`, together with the metaphysical
  conditionals `separates_of_characterIsFiberLocal`, `character_not_structural`,
  `phenomenalIsFiberLocal_iff_characterIsFiberLocal`,
  `separates_of_phenomenalIsFiberLocal`, and `phenomenal_not_structural`, should
  be axiom-free.

  STATUS: Builds cleanly under Lean 4.30.0 / Mathlib `v4.30.0`
  (commit c5ea00351c28e24afc9f0f84379aa41082b1188f) with no
  `sorry`/`admit`/`axiom`/`unsafe`. Reproduce with
  `lake exe cache get && lake build`; the axiom audit block at the end of the
  file reports the profile summarized above.
-/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Logic.Basic
-- Fallback if a lemma is not found: `import Mathlib`

set_option autoImplicit false

namespace OE

/-! ## 1. Schematic descent layer (paper §§2–3)

`Obs` is the type of observer-perspectives. The admissible transformations are
modelled, at this schematic level, by an equivalence relation: a `Setoid Obs`
whose quotient is the structural codomain `Str`. This matches the paper's
hedging that descent is "a quotient/descent construction along the relevant
action/groupoid, not necessarily a set-theoretic quotient." The genuine
group-action case is recovered in §2'. -/

section Schematic

variable {Obs : Type*} [s : Setoid Obs] {X : Type*}

/-- The structural quotient `S := O/≈` (paper Eq. (1)).

The base type `Obs` is an explicit argument so that the quotient (and hence its
`Setoid` instance) is always pinned at use sites; otherwise an occurrence of
`Str` with no constraining `proj` would leave the `Setoid Obs` instance stuck on
a metavariable. -/
abbrev Str (Obs : Type*) [inst : Setoid Obs] : Type _ := Quotient inst

/-- The projection `π : O → S` that forgets mode of givenness (paper Eq. (2), §2). -/
def proj : Obs → Str Obs := Quotient.mk s

/-- A candidate quantity is **invariant** if it is constant on
equivalence classes of admissible transformations. In the group-action
realization (§2′ below), this is the familiar condition `Q (g • o) = Q o`. -/
def Invariant (Q : Obs → X) : Prop := ∀ a b : Obs, a ≈ b → Q a = Q b

/-- A candidate quantity is **constant on fibers** if any two perspectives
with the same structural image receive the same value. -/
def ConstantOnFibers (Q : Obs → X) : Prop := ∀ a b : Obs, proj a = proj b → Q a = Q b

/-- A candidate quantity **descends** to the structural quotient if it
factors through `π` (the factorization condition in the paper's Quotient Test). -/
def Descends (Q : Obs → X) : Prop := ∃ Q' : Str Obs → X, Q = Q' ∘ proj

/-- A candidate quantity **separates a fiber** if it distinguishes two
perspectives with the same structural image (the would-be "phenomenal
discriminator" of §7). -/
def SeparatesAFiber (Q : Obs → X) : Prop := ∃ a b : Obs, proj a = proj b ∧ Q a ≠ Q b

/-- Invariance and constancy-on-fibers are the same condition, since
`π a = π b ↔ a ≈ b`. -/
theorem invariant_iff_constantOnFibers (Q : Obs → X) :
    Invariant Q ↔ ConstantOnFibers Q := by
  constructor
  · intro h a b hab
    exact h a b (Quotient.exact hab)
  · intro h a b hab
    exact h a b (Quotient.sound hab)

/-- The descent of an invariant quantity to the structural quotient
(the descended map `Q̃` of the Quotient Test). -/
def descend (Q : Obs → X) (h : Invariant Q) : Str Obs → X :=
  Quotient.lift Q fun _ _ hab => h _ _ hab

@[simp] theorem descend_proj (Q : Obs → X) (h : Invariant Q) (o : Obs) :
    descend Q h (proj o) = Q o := rfl

/-- **Quotient Test (existence).**
A quantity is invariant under admissible transformations iff it descends to
the structural quotient. -/
theorem quotientTest (Q : Obs → X) : Invariant Q ↔ Descends Q := by
  constructor
  · intro h
    refine ⟨descend Q h, ?_⟩
    funext o
    rfl
  · rintro ⟨Q', rfl⟩
    intro a b hab
    exact congrArg Q' (Quotient.sound hab)

/-- Two maps out of the quotient that agree after precomposition with `π`
are equal (`π` is surjective). The uniqueness half of the Quotient Test. -/
theorem descend_unique {Q'₁ Q'₂ : Str Obs → X}
    (h : ∀ o : Obs, Q'₁ (proj o) = Q'₂ (proj o)) : Q'₁ = Q'₂ :=
  funext (Quotient.ind h)

/-- **Quotient Test (existence + uniqueness).**
An invariant quantity descends to a *unique* map on the structural quotient. -/
theorem quotientTest_unique (Q : Obs → X) (h : Invariant Q) :
    ∃! Q' : Str Obs → X, Q = Q' ∘ proj := by
  refine ⟨descend Q h, ?_, ?_⟩
  · funext o; rfl
  · intro Q'' hQ''
    apply descend_unique
    intro o
    exact (congrFun hQ'' o).symm

/-- **Dilemma horn (a), §7.** If a quantity descends to the structural
quotient, it is *blind to the fiber*: it cannot distinguish two perspectives
once their structural image is fixed. -/
theorem fiber_blind {Q : Obs → X} (h : Descends Q) {a b : Obs}
    (hab : proj a = proj b) : Q a = Q b := by
  obtain ⟨Q', rfl⟩ := h
  exact congrArg Q' hab

/-- Contrapositive of `fiber_blind`: a quantity that separates two perspectives
in a common fiber cannot descend. -/
theorem not_descends_of_separates {Q : Obs → X} {a b : Obs}
    (hab : proj a = proj b) (hne : Q a ≠ Q b) : ¬ Descends Q :=
  fun h => hne (fiber_blind h hab)

/-- **A structural observable is necessarily fiber-blind (§7).** No quantity
can both descend to the structural quotient and separate a fiber. This is the
most article-ready form of horn (a). -/
theorem no_objective_fiber_sensitive_quantity {Q : Obs → X} :
    Descends Q → ¬ SeparatesAFiber Q := by
  intro hdesc hsep
  obtain ⟨a, b, hab, hne⟩ := hsep
  exact hne (fiber_blind hdesc hab)

/-- **No structural factorization of a fiber-sensitive quantity (§7 no-go).**
If `Q` separates a fiber, then `Q` is not of the form `Q' ∘ π` for any structural
`Q' : Str → X`: a fiber-sensitive quantity has no structural representative. -/
theorem no_factor_of_separates {Q : Obs → X} (h : SeparatesAFiber Q) :
    ∀ Q' : Str Obs → X, Q ≠ Q' ∘ proj := by
  intro Q' hQ
  obtain ⟨a, b, hab, hne⟩ := h
  exact hne (fiber_blind ⟨Q', hQ⟩ hab)

/-- **Dilemma horn (b), §7.** A quantity that tracks a
fiber-local difference (a "what-it-is-like" not visible in the public
structure) is not invariant — so it fails to define an objective observable. -/
theorem not_invariant_of_separatesAFiber {Q : Obs → X}
    (h : SeparatesAFiber Q) : ¬ Invariant Q := by
  intro hinv
  obtain ⟨a, b, hab, hne⟩ := h
  exact not_descends_of_separates hab hne ((quotientTest Q).mp hinv)

/-- The Quotient Test as a clean dichotomy (paper §3 and §7):
every candidate quantity either descends to the structural quotient (and is
then fiber-blind) or fails to be invariant. -/
theorem quotient_dichotomy (Q : Obs → X) : Descends Q ∨ ¬ Invariant Q := by
  by_cases h : Invariant Q
  · exact Or.inl ((quotientTest Q).mp h)
  · exact Or.inr h

/-- Classical converse of `not_invariant_of_separatesAFiber`: if a quantity is
not invariant, then it separates some fiber. Classical because the witness is
extracted from the negation of a universal statement. -/
theorem separatesAFiber_of_not_invariant {Q : Obs → X}
    (h : ¬ Invariant Q) : SeparatesAFiber Q := by
  classical
  by_contra hsep
  apply h
  intro a b hab
  by_contra hne
  exact hsep ⟨a, b, Quotient.sound hab, hne⟩

/-- **Strong Quotient Test dichotomy.** A candidate quantity either descends to
the structural quotient or it separates a fiber. This is sharper than
`quotient_dichotomy`: it names the actual obstruction (fiber sensitivity)
instead of mere non-invariance. -/
theorem quotient_dichotomy_strong (Q : Obs → X) :
    Descends Q ∨ SeparatesAFiber Q := by
  classical
  by_cases h : Invariant Q
  · exact Or.inl ((quotientTest Q).mp h)
  · exact Or.inr (separatesAFiber_of_not_invariant h)

/-- A quantity descends exactly when it does not separate any fiber: the
descent obstruction is fiber sensitivity, and nothing else. -/
theorem descends_iff_not_separatesAFiber (Q : Obs → X) :
    Descends Q ↔ ¬ SeparatesAFiber Q := by
  classical
  constructor
  · exact no_objective_fiber_sensitive_quantity
  · intro hno
    refine (quotientTest Q).mp ?_
    intro a b hab
    by_contra hne
    exact hno ⟨a, b, Quotient.sound hab, hne⟩

end Schematic

/-! ## 2'. Group-action realization (§2, "G a symmetry group")

The schematic Setoid is realized by a genuine group action: the orbit relation
of `G ⟳ Obs`. Here "invariant" is the literal `Q (g • o) = Q o`, and the
Quotient Test transfers verbatim to the orbit space `Obs / G`. -/

section GroupAction

open MulAction

variable {G : Type*} [Group G] {Obs : Type*} [MulAction G Obs] {X : Type*}

/-- Invariance under the group of admissible transformations: `Q (g • o) = Q o`
for all `g : G` and `o : Obs`. -/
def GInvariant (Q : Obs → X) : Prop := ∀ (g : G) (o : Obs), Q (g • o) = Q o

/-- Group-invariance coincides with invariance under the orbit relation. The
operative setoid `orbitRel G Obs` (admissible transformations = the group
action) is passed explicitly to the schematic `Invariant`, so no local
instance or `set_option` is needed: the group case is a clean specialization. -/
theorem ginvariant_iff_invariant (Q : Obs → X) :
    GInvariant (G := G) Q ↔ Invariant (s := orbitRel G Obs) Q := by
  constructor
  · intro h a b hab
    -- `hab : a ≈ b` is, definitionally, `a ∈ orbit G b` (`orbitRel_apply` is `Iff.rfl`).
    have hmem : a ∈ orbit G b := hab
    obtain ⟨g, hg⟩ := hmem
    rw [← hg]
    exact h g b
  · intro h g o
    have hmem : g • o ∈ orbit G o := mem_orbit o g
    exact h _ _ hmem

/-- **Quotient Test for genuine symmetry groups.** A quantity is invariant
under the admissible group action iff it descends to the orbit space
`Obs / G` (i.e. the quotient by `orbitRel G Obs`). -/
theorem quotientTest_group (Q : Obs → X) :
    GInvariant (G := G) Q ↔ Descends (s := orbitRel G Obs) Q :=
  (ginvariant_iff_invariant Q).trans (quotientTest (s := orbitRel G Obs) Q)

end GroupAction

/-! ## 3. Degeneration of the projection in the limit (paper §6)

`I` is the OE-relevant invariant signature read off the structural quotient
(symmetry data, orbit-type complexity, `dim Aut(S)`, ...). The
`S_min` regime of "maximal symmetry / no remaining OE-relevant distinctions"
is modelled here by the strong *endpoint* condition that `I` is globally
constant. This is a toy limit, NOT a formalization of `S_min` itself: it omits
the order `≻_I` on invariant signatures, descending chains, minimality, and
automorphism growth. These are future refinements, not part of the present
machine-checked core. -/

section Degeneration

variable {Obs : Type*} [s : Setoid Obs] {Inv : Type*}

/-- The invariant signature **collapses** when it cannot distinguish any two
structural classes. This is a toy formal *endpoint* of the `S_min` discussion —
the strong condition that `I` is globally constant (`Aut(S)` is `I`-maximal, the
remaining distinctions are quotiented out) — not the full order-theoretic
`S_min` of paper §6. -/
def Collapses (I : Str Obs → Inv) : Prop := ∀ x y : Str Obs, I x = I y

/-- Under collapse, admissible base change in `Obs` induces no variation in the
invariant signature of the structural image (`I(π o)` ceases to vary in the collapsed endpoint of paper §6). -/
theorem collapse_const (I : Str Obs → Inv) (h : Collapses I) (a b : Obs) :
    I (proj a) = I (proj b) := h _ _

/-- Under collapse, every quantity assembled from the invariant signature is
non-discriminating: invariance constraints become vacuous. -/
theorem collapse_no_discrimination {X : Type*} (I : Str Obs → Inv) (h : Collapses I)
    (f : Inv → X) (a b : Obs) :
    (f ∘ I ∘ proj) a = (f ∘ I ∘ proj) b :=
  congrArg f (collapse_const I h a b)

/-- Under collapse, no nonconstant perspective-quantity factors through the
collapsed invariant signature `I ∘ π`. This is the formal core of the paper's
phenomenal-time gesture in §6: if a temporal-character map still varies, then
that variation is not represented by the collapsed structural signature. -/
theorem no_factor_through_collapsed_signature {X : Type*} (I : Str Obs → Inv)
    (h : Collapses I) (Q : Obs → X) (hQ : ∃ a b : Obs, Q a ≠ Q b) :
    ∀ F : Inv → X, Q ≠ F ∘ I ∘ proj := by
  intro F hfac
  obtain ⟨a, b, hneq⟩ := hQ
  apply hneq
  calc
    Q a = (F ∘ I ∘ proj) a := congrFun hfac a
    _ = (F ∘ I ∘ proj) b := collapse_no_discrimination I h F a b
    _ = Q b := (congrFun hfac b).symm

/-- OE-linked time as *registered* structural change (paper §6): a base change
`a ⤳ b` registers iff it alters the invariant signature of the structural
image. -/
def Registers (I : Str Obs → Inv) (a b : Obs) : Prop := I (proj a) ≠ I (proj b)

/-- **Time-degeneration corollary (paper §6).** In the collapsed regime no base
change registers, so the OE notion of time becomes vacuous. -/
theorem time_degenerates (I : Str Obs → Inv) (h : Collapses I) (a b : Obs) :
    ¬ Registers I a b :=
  fun hreg => hreg (collapse_const I h a b)

end Degeneration

/-! ## 4. Non-structural facts under forgetfulness (paper §4) — structural core

The forgetfulness constraint (F1) says `π` is non-injective on objects. We show
its precise consequence: as soon as `π` is forgetful, there are facts about
perspectives — paradigmatically *which* perspective one occupies — that do
**not** descend to the structural quotient. Such facts are invisible to every
structural quantity and therefore survive any collapse of structure. This is
the formal skeleton onto which the metaphysical reading of §5 is laid (next
section). -/

section Forgetfulness

variable {Obs : Type*} [s : Setoid Obs]

/-- Forgetfulness constraint (F1, paper §4): distinct perspectives can share a
structural image. -/
def Forgetful : Prop := ∃ o₁ o₂ : Obs, o₁ ≠ o₂ ∧ proj o₁ = proj o₂

/-- **Non-structural facts exist under forgetfulness.** If `π` is forgetful,
some predicate on perspectives does not descend to the structural quotient:
no structural predicate `P'` on `Str` satisfies `P = P' ∘ π`. -/
theorem exists_nonstructural_of_forgetful (h : Forgetful (Obs := Obs)) :
    ∃ P : Obs → Prop, ∀ P' : Str Obs → Prop, P ≠ P' ∘ proj := by
  obtain ⟨o₁, o₂, hne, hpr⟩ := h
  refine ⟨fun o => o = o₁, fun P' hP => hne ?_⟩
  have e₁ : (o₁ = o₁) = P' (proj o₁) := congrFun hP o₁
  have e₂ : (o₂ = o₁) = P' (proj o₂) := congrFun hP o₂
  have hmid : P' (proj o₁) = P' (proj o₂) := congrArg P' hpr
  have hchain : (o₁ = o₁) = (o₂ = o₁) := e₁.trans (hmid.trans e₂.symm)
  have hcast : o₂ = o₁ := cast hchain rfl
  exact hcast.symm

end Forgetfulness

/-! ## 5. Metaphysical layer — ASSUMPTIONS, NOT THEOREMS (paper §5)

Everything below depends on the paper's metaphysical premises. They are
recorded as explicit hypotheses/definitions so that the *conditional* shape of
the argument is machine-checked, while the verified core (§§1–4) stays clean.
**No global `axiom` is introduced here.** -/

namespace Metaphysics

section
variable {Obs : Type*} [s : Setoid Obs]

/-- **Character-valued fiber-locality (primary premise, paper §5).**
A richer codomain can express variation in phenomenal character inside a fiber
without requiring one fiber-mate to be non-phenomenal. This is the codomain-
generic form already available in the descent core. -/
def CharacterIsFiberLocal {C : Type*} (Character : Obs → C) : Prop :=
  ∃ o₁ o₂ : Obs, proj o₁ = proj o₂ ∧ Character o₁ ≠ Character o₂

/-- The character-valued fiber-locality premise *is* a fiber separation for
`Character`. This bridge keeps the file architecture explicit: metaphysical
premises enter through named bridge lemmas, while the no-go step itself remains
domain-neutral. -/
theorem separates_of_characterIsFiberLocal {C : Type*} (Character : Obs → C)
    (h : CharacterIsFiberLocal Character) :
    SeparatesAFiber Character := h

/-- **No structural representative for fiber-local phenomenal character.**
If a character-valued map separates a fiber, then no structural map on the
quotient represents it. This is the main phenomenal application in the paper;
the Prop-valued zombie-pair version below is its bivalent special case. -/
theorem character_not_structural {C : Type*} (Character : Obs → C)
    (h : CharacterIsFiberLocal Character) :
    ∀ C' : Str Obs → C, Character ≠ C' ∘ proj :=
  no_factor_of_separates
    (Q := Character)
    (separates_of_characterIsFiberLocal (Character := Character) h)

-- `Phenomenal o`: there is something it is like for actuality to obtain at
-- perspective `o` (paper §5). An opaque, ontologically primitive predicate — in
-- particular it is *not assumed* to descend to the structural quotient.
variable (Phenomenal : Obs → Prop)

/-- **Prop-valued fiber-locality of phenomenality (special case, paper §5).**
Phenomenality is *not constant on the fibers of* `π`: some two perspectives that
share a structural image are assigned different phenomenal verdicts.

Because `Phenomenal : Obs → Prop`, this premise is strong. Under the usual
extensional/classical reading of propositions, `Phenomenal o₁ ≠ Phenomenal o₂`
has the force of a local zombie-pair premise: within one structural fiber, one
perspective is phenomenally occupied and the other is not. Lean itself only uses
the displayed inequality as an explicit hypothesis; it does not prove that such
a pair exists.

Definitionally this premise is `CharacterIsFiberLocal Phenomenal`, and hence
also `SeparatesAFiber Phenomenal`; stating it in phenomenal vocabulary keeps the
metaphysical commitment legible and separate from the domain-neutral core. -/
def PhenomenalIsFiberLocal : Prop :=
  ∃ o₁ o₂ : Obs, proj o₁ = proj o₂ ∧ Phenomenal o₁ ≠ Phenomenal o₂

/-- The Prop-valued phenomenality premise is exactly the character-valued
fiber-locality premise specialized to the codomain `Prop`. This theorem records
in Lean the paper's claim that the local-zombie premise is the bivalent special
case of the codomain-generic character premise. -/
theorem phenomenalIsFiberLocal_iff_characterIsFiberLocal :
    PhenomenalIsFiberLocal Phenomenal ↔ CharacterIsFiberLocal Phenomenal := Iff.rfl

/-- The Prop-valued fiber-locality premise *is* a fiber separation for
`Phenomenal` (the two definitions are syntactically the same `∃`, only the
vocabulary differs). This is the named bridge where the Prop-valued
metaphysical premise enters the formal argument; every downstream step is the
domain-neutral descent core. -/
theorem separates_of_phenomenalIsFiberLocal
    (h : PhenomenalIsFiberLocal Phenomenal) :
    SeparatesAFiber Phenomenal := h

/-- **Conditional non-structurality of Prop-valued phenomenality (paper §5).**
GIVEN that phenomenality is fiber-local in the Prop-valued sense, the predicate
`Phenomenal` does not descend to the structural quotient: no structural property
captures it. The proof passes through
`phenomenalIsFiberLocal_iff_characterIsFiberLocal` and then applies the
character-valued theorem `character_not_structural`, so the Prop-valued theorem
is literally a corollary of the codomain-generic result. -/
theorem phenomenal_not_structural (h : PhenomenalIsFiberLocal Phenomenal) :
    ∀ P' : Str Obs → Prop, Phenomenal ≠ P' ∘ proj :=
  character_not_structural
    (Character := Phenomenal)
    ((phenomenalIsFiberLocal_iff_characterIsFiberLocal
      (Phenomenal := Phenomenal)).mp h)

end

end Metaphysics

/-! ## Axiom audit (run in your Mathlib environment)

Expected results of this audit (to be re-run under Lean 4.30.0, Mathlib `v4.30.0`):

§8.1 Core quotient/descent theorems — constructive modulo `Quot.sound`:
  `quotientTest`, `quotientTest_unique`, `not_invariant_of_separatesAFiber`
                                       →  `[Quot.sound]`
  `fiber_blind`, `no_factor_of_separates`,
  `no_objective_fiber_sensitive_quantity`,
  `exists_nonstructural_of_forgetful`,
  `no_factor_through_collapsed_signature`, `time_degenerates`
                                       →  no axioms at all.

§8.2 Classical corollaries — `Classical.choice` enters via `by_cases`/`by_contra`:
  `quotient_dichotomy`, `quotient_dichotomy_strong`,
  `separatesAFiber_of_not_invariant`, `descends_iff_not_separatesAFiber`,
  `quotientTest_group` (also pulls classical group-theory machinery)
                                       →  `[propext, Classical.choice, Quot.sound]`

§8.3 Metaphysical conditional layer — constructive: the Prop-valued and
  character-valued premises are definitionally fiber separations (the bridge
  lemmas are `:= h`), and each no-go is a direct specialization of the
  axiom-free `no_factor_of_separates` or `character_not_structural`:
  `separates_of_characterIsFiberLocal`, `character_not_structural`,
  `phenomenalIsFiberLocal_iff_characterIsFiberLocal`,
  `separates_of_phenomenalIsFiberLocal`, `phenomenal_not_structural`
                                       →  no axioms at all. -/

-- §8.1 core
-- #print axioms OE.quotientTest
-- #print axioms OE.quotientTest_unique
-- #print axioms OE.fiber_blind
-- #print axioms OE.not_invariant_of_separatesAFiber
-- #print axioms OE.no_factor_of_separates
-- #print axioms OE.no_objective_fiber_sensitive_quantity
-- #print axioms OE.exists_nonstructural_of_forgetful
-- #print axioms OE.no_factor_through_collapsed_signature
-- #print axioms OE.time_degenerates
-- §8.2 classical corollaries
-- #print axioms OE.separatesAFiber_of_not_invariant
-- #print axioms OE.quotient_dichotomy
-- #print axioms OE.quotient_dichotomy_strong
-- #print axioms OE.descends_iff_not_separatesAFiber
-- #print axioms OE.quotientTest_group
-- §8.3 metaphysical conditional layer
-- #print axioms OE.Metaphysics.separates_of_characterIsFiberLocal
-- #print axioms OE.Metaphysics.character_not_structural
-- #print axioms OE.Metaphysics.phenomenalIsFiberLocal_iff_characterIsFiberLocal
-- #print axioms OE.Metaphysics.separates_of_phenomenalIsFiberLocal
-- #print axioms OE.Metaphysics.phenomenal_not_structural

end OE
