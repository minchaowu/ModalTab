import defs

structure KT (states : Type) extends kripke states :=
(refl  : reflexive rel)
