module TLA.Lemmas where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (sym)
open import Relation.Nullary
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Function.Inverse hiding (sym)
open import Function
open import Data.Fin.Permutation
open import TLA.Def
open import TLA.Refine
open import Data.List hiding (all)
open import Data.Sum
open import Data.Product
open import Level renaming (zero to lzero ; suc to lsuc)
open import Data.Maybe

open import LTL.Core
open import LTL.Stateless
open import LTL.Future
open import LTL.Sum
open import LTL.Product
open import LTL.Globally


b : ∀{α} → {varsB varsA varsC : LSet {α}}
    → {refm-ba : System varsB → System varsA} → {refm-ac : System varsA → System varsC}
    → {specA : Spec varsA} → {specB : Spec varsB} → {specC : Spec varsC}
    → {gcondB : GCond varsB} → {gcondA : GCond varsA}
    → RSpec refm-ba gcondB specA specB → RSpec refm-ac gcondA specC specA → {!RSpec ?  !}
b = {!!}

{--
Ea ∧ Ma   Eb ∧ Mb
a b variables

a ∧ b = c common variables.

Since Ea are not implemented, we allow the remaining vars b - c to do whatever they want.
Ma is to be implemented, so we expect to have interleaving between different components. All other variables 
(b - c) are constant.

Ea' ⊂ Ea Ear, Eb' ⊂ Eb Ebr

Ea' ∧ (Ma ⇒ Eb')
Eb' ∧ Mb ⇒ Ea' ∧ Eb'

Ma ∧ Mb ⇒ Ea' ∧ Ma
Ma ∧ Mb ⇒ Eb' ∧ Mb

--}
