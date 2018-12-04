module TLA.Refine where

open import Level renaming (zero to lzero ; suc to lsuc ; Lift to ℓ↑)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat
open import Data.Unit
open import Data.Sum
open import Data.Vec hiding ([_] ; split)

open import LTL.Core
open import LTL.Stateless

open import TLA.Def
open import TLA.Utils


-- Should we externalize RE ? It is used by RSpec already? Do we know RE before hand?
record RefAction {α n k}{varsB : VSet {α} k} {varsA : VSet {α} n} 
                 {B : Set α} (refm : System varsB → System varsA) (actA : Action B varsA) : Set (lsuc α) where
  field
    RE : Set α
    ract : Action RE varsB
    par : (e : RE) → (sys : System varsB) → B
    gcond : (e : RE) → (sys : System varsB) → Set α
    embed : (e : RE) → (sys : System varsB) → (gcnd : gcond e sys) → (nsys : System varsB)
            → cond ract e sys × resp ract e sys nsys
            → (cond actA) (par e sys) (refm sys) × (resp actA) (par e sys) (refm sys) (refm nsys)
open RefAction public




refStAction : ∀{n k} → {varsB : VSet n} → {varsA : VSet k}
              → (refm : System varsB → System varsA) → RefAction refm stAction
RE (refStAction refm) = ⊤
ract (refStAction refm) = stAction
par (refStAction refm) e sys = tt
gcond (refStAction refm) e sys = ⊤
embed (refStAction refm) e sys gcnd nsys (fst , snd)
  = tt , subst (λ z → refm sys ≡ refm z all) (pEq⇒Eq snd) refl-all


refStAction′ : ∀{α n k} → {varsB : VSet {α} n} → {varsA : VSet {α} k}
              → (refm : System varsB → System varsA) → RefAction refm stAction′
RE (refStAction′ refm) = ℓ↑ _ ⊤
ract (refStAction′ refm) = stAction′
par (refStAction′ refm) e sys = lift tt
gcond (refStAction′ refm) e sys = ℓ↑ _ ⊤
embed (refStAction′ refm) e sys gcnd nsys (fst , snd)
  = (lift tt) , subst (λ z → refm sys ≡ refm z all) (pEq⇒Eq snd) refl-all



infixr 5 _∷ᵣₛₚ_
infixr 5 _m∷ᵣₛₚ_
data RSpec {α n k} {varsB : VSet {α} n} {varsA : VSet {α} k}
           (refm : System varsB → System varsA) : ∀{el bl} → {PB : VSet {α} bl} → (PE : VSet {α} el)
           → (spec : Spec varsA PB) → Set (lsuc α) where
  _m∷ᵣₛₚ_ : ∀{B act bl PB el PE spec} → (ref : RefAction {B = B} refm act)
            → (rspec : RSpec refm {el = el} {bl = suc bl} {PB = B ∷ PB} PE (act ∷ₛₚ spec))
            → RSpec refm {PB = B ∷ PB} (RE ref ∷ PE) (act ∷ₛₚ spec)
  _∷ᵣₛₚ_ : ∀{B act bl PB el PE spec} → (ref : RefAction {B = B} refm act)
           → (rspec : RSpec refm {el = el} {bl = bl} {PB = PB} PE spec)
           → RSpec refm {PB = B ∷ PB} (RE ref ∷ PE) (act ∷ₛₚ spec)
  []ᵣₛₚ : RSpec refm [] []ₛₚ


exSpec : ∀{α lb la varsB varsA el PE bl PB spec} → {refm : System {α} {lb} varsB → System {α} {la} varsA}
         → RSpec refm {el = el} {bl = bl} {PB = PB} PE spec
         → Spec varsB PE
exSpec (ref m∷ᵣₛₚ rspec) = (ract ref) ∷ₛₚ (exSpec rspec)
exSpec (ref ∷ᵣₛₚ rspec) = (ract ref) ∷ₛₚ (exSpec rspec)
exSpec []ᵣₛₚ = []ₛₚ

exGcond : ∀{α lb la varsB varsA el PE bl PB spec} → {refm : System {α} {lb} varsB → System {α} {la} varsA}
          → RSpec refm {el = el} {bl = bl} {PB = PB} PE spec
          → (PE toUS) → (sys : System varsB) → Set α
exGcond (ref m∷ᵣₛₚ rspec) (e ←u) sys = gcond ref e sys
exGcond (ref m∷ᵣₛₚ rspec) (u→ pe) sys = exGcond rspec pe sys
exGcond (ref ∷ᵣₛₚ rspec) (e ←u) sys = gcond ref e sys
exGcond (ref ∷ᵣₛₚ rspec) (u→ pe) sys = exGcond rspec pe sys
exGcond []ᵣₛₚ (lift ()) sys


exPar :  ∀{α lb la varsB varsA el PE bl PB spec} → {refm : System {α} {lb} varsB → System {α} {la} varsA}
         → RSpec refm {el = el} {bl = bl} {PB = PB} PE spec
         → (PE toUS) → (System varsB) → (PB toUS)
exPar (ref m∷ᵣₛₚ rspec) (e ←u) sys = par ref e sys ←u
exPar (ref m∷ᵣₛₚ rspec) (u→ pe) sys = exPar rspec pe sys
exPar (ref ∷ᵣₛₚ rspec) (e ←u) sys = par ref e sys ←u
exPar (ref ∷ᵣₛₚ rspec) (u→ pe) sys = u→ exPar rspec pe sys


refTh : ∀{α lb la varsB varsA el PE bl PB spec} → {refm : System {α} {lb} varsB → System {α} {la} varsA}
             → (rspec : RSpec refm {el = el} {bl = bl} {PB = PB} PE spec)
             → (sys nsys : (System varsB)) → (pe : (PE toUS)) → exGcond rspec pe sys
             → (exSpec rspec  $ₛₚ pe) sys nsys → (spec $ₛₚ (exPar rspec pe sys)) (refm sys) (refm nsys)
refTh (ref m∷ᵣₛₚ rspec) sys nsys (e ←u) gcnd rst = embed ref e sys gcnd nsys rst
refTh (ref m∷ᵣₛₚ rspec) sys nsys (u→ pe) gcnds rst = refTh rspec sys nsys pe gcnds rst
refTh (ref ∷ᵣₛₚ rspec) sys nsys (e ←u) gcnd rst = embed ref e sys gcnd nsys rst
refTh (ref ∷ᵣₛₚ rspec) sys nsys (u→ pe) gcnds rst = refTh rspec sys nsys pe gcnds rst
refTh []ᵣₛₚ sys nsys () rst



trefTh : ∀{α lb la varsB varsA el PE bl PB spec} → {refm : System {α} {lb} varsB → System {α} {la} varsA}
             → (rspec : RSpec refm {el = el} {bl = bl} {PB = PB} PE spec)
             → (beh : (System varsB) ʷ) → (pe : (PE toUS) ʷ) → [ ⟨ exGcond rspec ⟩ $ pe $ beh ]
             → [ ((exSpec rspec  $ₛₚₜ pe) beh) ⇒ ((spec $ₛₚₜ (⟨ exPar rspec ⟩ $ pe $ beh) ) (⟨ refm ⟩ $ beh)) ]
trefTh rspec beh pe gcnd n rst = refTh rspec(beh n) (beh (suc n)) (pe n) (gcnd n) rst
