import defs

structure S4 (states : Type) extends kripke states :=
(refl  : reflexive rel)
(trans : transitive rel)
