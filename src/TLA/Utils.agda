module TLA.Utils where

open import TLA.Def
open import Prelude.Fin public


proj : ∀{n} → {PE : VSet {α} n} → System PE → (i : Fin n) → indexVec PE i
proj {PE = []} sys ()
proj {PE = E ∷ PE} sys zero = fst sys
proj {PE = E ∷ PE} sys (suc i) = proj (snd sys) i


_except_!=_ : ∀{n} → {PE : VSet {α} n} → System PE → (i : Fin n) → indexVec PE i → System PE
_except_!=_ {PE = []} sys () nv
_except_!=_ {PE = E ∷ PE} sys zero nv = nv , snd sys
_except_!=_ {PE = E ∷ PE} sys (suc i) nv = fst sys , snd sys except i != nv 
