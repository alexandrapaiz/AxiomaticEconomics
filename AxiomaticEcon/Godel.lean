namespace Incompleteness

constant FormalSystem : Type
constant Provable : FormalSystem → Prop → Prop
constant omegaConsistent : FormalSystem → Prop
constant recursivelyEnumerable : FormalSystem → Prop

axiom godelFirst :
  ∀ S : FormalSystem,
    omegaConsistent S →
    recursivelyEnumerable S →
    ∃ G : Prop, ¬ Provable S G ∧ ¬ Provable S (¬ G)

end Incompleteness
