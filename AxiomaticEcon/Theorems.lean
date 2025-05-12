import AxiomaticEcon.Core

namespace AxiomaticEconomics

/--
`Values a m e` means that actor `a` values means `m` **because** it helps achieve end `e`.

In Austrian economics, means have no inherent worth; their value is derived entirely
from the ends they are expected to serve.
We capture that link by re‑using `Purposeful`.
-/
def Values (a : Actor) (m : Means) (e : End) : Prop :=
  Purposeful a e m

/--
`PrefersMeans a m₁ m₂` encodes that actor `a` subjectively ranks means `m₁`
higher than means `m₂`.  It is an ordinal, not cardinal, relation—just like
`Prefers` for ends.
-/
axiom PrefersMeans : Actor → Means → Means → Prop

/-! ----------------------------------------------------------------
    ## Time‑Preference Section
    ----------------------------------------------------------------

   The next group of definitions captures the quintessential Austrian
   insight that—ceteris paribus—actors prefer earlier attainment of a
   given end to later attainment.  We formalise this in four steps:

   1.  A simple “earlier than” relation on `Timepoint`s.
   2.  A `TimedEnd` structure bundling an `End` with a `Timepoint`.
   3.  A primitive preference relation for timed ends (we reuse `Prefers`).
   4.  The **Time‑Preference Axiom**.
-/

/-- `Earlier t₁ t₂` holds when `t₁` occurs strictly before `t₂`. -/
def Earlier (t₁ t₂ : Timepoint) : Prop :=
  t₁.t < t₂.t

/--
`TimedEnd` pairs an underlying end with a concrete moment in time.
`{base := e, time := t}` should be read as “achieving end `e` **at** time `t`.”
We avoid the field name `at` because it clashes with Lean’s syntax.
-/
structure TimedEnd where
  base : End
  time : Timepoint
deriving Repr

/--
For convenience we coerce `TimedEnd` into `End` in order to reuse
the existing `Prefers` relation without defining a separate one.
-/
instance : Coe TimedEnd End where
  coe := TimedEnd.base

/-- **Axiom (Time Preference)**

Ceteris paribus, an actor prefers achieving the same end sooner
rather than later.  Formally, if `t₁` is earlier than `t₂`, then
the timed end achieved at `t₁` is preferred to that achieved at `t₂`.
-/
axiom TimePreference :
  ∀ (a : Actor) (e : End) (t₁ t₂ : Timepoint),
    Earlier t₁ t₂ →
    Prefers a ({ base := e, time := t₁ } : TimedEnd)
             ({ base := e, time := t₂ } : TimedEnd)

/-! ----------------------------------------------------------------
    ## Preference‑Consistency Axioms
    ----------------------------------------------------------------
    To give our ordinal rankings minimal logical coherence we add
    *transitivity* for both ends and means, plus the trivial property
    that “earlier” on `Timepoint`s is transitive by arithmetic.
-/

/-‑- Transitivity for preferences over ends. -/
axiom Prefers_trans :
  ∀ {a : Actor} {e₁ e₂ e₃ : End},
    Prefers a e₁ e₂ →
    Prefers a e₂ e₃ →
    Prefers a e₁ e₃

/-- Irreflexivity for preferences over ends. No end is strictly preferred to itself. -/
axiom Prefers_irrefl :
  ∀ {a : Actor} {e : End}, ¬ Prefers a e e

/-- Transitivity for preferences over means. -/
axiom PrefersMeans_trans :
  ∀ {a : Actor} {m₁ m₂ m₃ : Means},
    PrefersMeans a m₁ m₂ →
    PrefersMeans a m₂ m₃ →
    PrefersMeans a m₁ m₃

/-- Irreflexivity for preferences over means. No means is strictly preferred to itself. -/
axiom PrefersMeans_irrefl :
  ∀ {a : Actor} {m : Means}, ¬ PrefersMeans a m m

/-‑- *Earlier* is itself transitive because it is `<` on naturals. -/
lemma earlier_trans {t₁ t₂ t₃ : Timepoint} :
    Earlier t₁ t₂ → Earlier t₂ t₃ → Earlier t₁ t₃ := by
  unfold Earlier
  exact Nat.lt_trans

/-- *Earlier* is irreflexive: no point in time is earlier than itself. -/
lemma earlier_irrefl {t : Timepoint} : ¬ Earlier t t := by
  unfold Earlier; exact Nat.lt_irrefl _

/-! ----------------------------------------------------------------
    ## Choice and Revealed Preference
    ----------------------------------------------------------------
    We introduce a primitive binary-choice relation and the classic
    Revealed‑Preference axiom so we can derive WARP.
-/

/-- `Chooses a e₁ e₂` means actor `a`, when offered {e₁, e₂}, selects `e₁`. -/
axiom Chooses : Actor → End → End → Prop

/--
**Axiom (Revealed Preference)** – If `a` chooses `e₁` over `e₂`, then
either `a` strictly prefers `e₁` to `e₂` or the two ends coincide.
-/
axiom RevealedPref :
  ∀ {a : Actor} {e₁ e₂ : End},
    Chooses a e₁ e₂ →
    (Prefers a e₁ e₂) ∨ (e₁ = e₂)

/--
**Theorem (WARP)** – Weak Axiom of Revealed Preference.

An actor cannot choose `e₁` over `e₂` and later choose `e₂` over `e₁`
unless `e₁ = e₂`.
-/
theorem WARP
    {a : Actor} {e₁ e₂ : End}
    (h₁ : Chooses a e₁ e₂)
    (h₂ : Chooses a e₂ e₁) :
    e₁ = e₂ := by
  have h₁' := RevealedPref h₁
  have h₂' := RevealedPref h₂
  cases h₁' with
  | inl pref12 =>
      cases h₂' with
      | inl pref21 =>
          have contra := Prefers_trans pref12 pref21
          have absurd := Prefers_irrefl (a := a) (e := e₁)
          exact (absurd contra).elim
      | inr eq => exact eq.symm
  | inr eq => exact eq

/--
**Lemma (Time‑Preference transitivity)**

If `t₁` is earlier than `t₂` and `t₂` is earlier than `t₃`, then,
by the Time‑Preference axiom and transitivity of `Earlier`, the actor
prefers achieving the given end at `t₁` over achieving it at `t₃`.
-/
lemma time_preference_trans
    {a : Actor} {e : End} {t₁ t₂ t₃ : Timepoint}
    (h₁ : Earlier t₁ t₂) (h₂ : Earlier t₂ t₃) :
    Prefers a ({ base := e, time := t₁ } : TimedEnd)
            ({ base := e, time := t₃ } : TimedEnd) := by
  have h13 : Earlier t₁ t₃ := earlier_trans h₁ h₂
  exact TimePreference a e t₁ t₃ h13

/--
**Axiom (Value Derived from Ends)**

If actor `a` values means `m₁` for end `e₁`,
and values means `m₂` for end `e₂`,
and `a` prefers `e₁` over `e₂`,
then `a` also prefers the corresponding means `m₁` over `m₂`.

This formalises marginal utility: the ordinal ranking of ends induces an
ordinal ranking of the means that help realise those ends.
-/
axiom ValueDerivedFromEnds :
  ∀ {a : Actor} {m₁ m₂ : Means} {e₁ e₂ : End},
    Values a m₁ e₁ →
    Values a m₂ e₂ →
    Prefers a e₁ e₂ →
    PrefersMeans a m₁ m₂

/--
**Theorem (Marginal Utility)**

Given an actor `a` who values means `m₁` for end `e₁`
and means `m₂` for end `e₂`,
if `a` prefers `e₁` over `e₂`, then `a` prefers `m₁` over `m₂`.

The proof is immediate from the `ValueDerivedFromEnds` axiom.
-/
theorem marginal_utility
    {a : Actor} {m₁ m₂ : Means} {e₁ e₂ : End}
    (h₁ : Values a m₁ e₁)
    (h₂ : Values a m₂ e₂)
    (h₃ : Prefers a e₁ e₂) :
    PrefersMeans a m₁ m₂ :=
  ValueDerivedFromEnds h₁ h₂ h₃


/-! ----------------------------------------------------------------
    ## Opportunity‑Cost Lemma
    ----------------------------------------------------------------
    Choosing one means for an end precludes simultaneously using a
    mutually‑exclusive alternative.  This captures opportunity cost in
    purely ordinal terms.
-/

/-- `MutuallyExclusive m₁ m₂` asserts that the same actor cannot employ
    means `m₁` and `m₂` at the same time (e.g. one unit of a good cannot
    be consumed in two different uses). -/
axiom MutuallyExclusive : Means → Means → Prop

/--
**Axiom (Exclusive Use)**

If two means are mutually exclusive, an actor cannot pursue two actions
that depend on those means at the same time.
-/
axiom ExclusiveUse :
  ∀ {a : Actor} {m₁ m₂ : Means} {e₁ e₂ : End},
    MutuallyExclusive m₁ m₂ →
    Purposeful a e₁ m₁ →
    Purposeful a e₂ m₂ →
    False

/--
**Lemma (Opportunity Cost)**

Suppose
* means `m₁` and `m₂` are mutually exclusive,
* actor `a` prefers `m₁` over `m₂`,
* the actor is currently acting with `m₁` to achieve `e₁`.

Then it is impossible for the actor to *simultaneously* pursue any end
using `m₂`.  The foregone action with `m₂` represents the opportunity
cost of employing `m₁`.
-/
lemma opportunity_cost
    {a : Actor} {m₁ m₂ : Means} {e₁ e₂ : End}
    (hex : MutuallyExclusive m₁ m₂)
    (hpref : PrefersMeans a m₁ m₂)
    (hact : Purposeful a e₁ m₁) :
    ¬ Purposeful a e₂ m₂ :=
by
  intro h₂
  exact ExclusiveUse hex hact h₂

end AxiomaticEconomics
