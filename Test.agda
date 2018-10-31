module Test where

open import LTL.Stateless
open import LTL.Future
open import LTL.Causal
open import LTL.Product
open import LTL.Decoupled
open import LTL.CatHetSt
open import LTL.PolConsts


open import Prelude.Product
open import Prelude.Fin
open import Prelude.Vec
open import Prelude.Semiring
open import Prelude.Functor
open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Nat.Properties
open import Data.These hiding ( map ) 

open import Agda.Primitive

open import Prelude.Sum renaming (Either to _⊎_)
open import Prelude.Empty
open import Prelude.Function

open import Def


data Perit (n : Nat) : Set where
  per : ∀ {k} → k + k + (suc zero) ≡ n → Perit n

data Art (n : Nat) : Set where
  art : ∀ {k} → k + k ≡ n → Art n


varS : Vec Set 1
varS = Nat ∷ []

action1 : Action varS
cond action1 = Perit
resp action1 = λ ov nv → Art nv

action2 : Action varS
cond action2 = Art
resp action2 = λ ov nv → Perit nv

specS : Spec varS 1
specS = action1 ∷ action2 ∷ []

