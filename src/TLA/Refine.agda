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

GCond : ∀{α k} → (varsB : VSet {α} k) → Set (lsuc α)
GCond {α} varsB = (sys : System varsB) → Set α

GCondV : ∀{α k} → (varsB : VSet {α} k) → ∀ gk → Set (lsuc α)
GCondV {α} varsB gk = (sys : System varsB) → VSet {α} gk


-- Should we externalize RE ? It is used by RSpec already? Do we know RE before hand?
record RefAction {α n k}{varsB : VSet {α} k} {varsA : VSet {α} n} 
                 {B : Set α} (refm : System varsB → System varsA)
                 (gcond : GCond varsB) (actA : Action B varsA) : Set (lsuc α) where
  field
    RE : Set α
    ract : Action RE varsB
    par : (e : RE) → (sys : System varsB) → B
    gcondInd : (e : RE) → (sys : System varsB) → (nsys : System varsB)
               → (rst : cond ract e sys × resp ract e sys nsys) → (ind : gcond sys) → gcond nsys
    embed : (e : RE) → (sys : System varsB) → (nsys : System varsB) → (gcnd : gcond sys)
            → (rst : cond ract e sys × resp ract e sys nsys)
            → (cond actA) (par e sys) (refm sys) × (resp actA) (par e sys) (refm sys) (refm nsys)
open RefAction public




refStAction : ∀{n k} → {varsB : VSet n} → {varsA : VSet k}
              → (refm : System varsB → System varsA) → (gcond : GCond varsB) → RefAction refm gcond stAction
RE (refStAction refm gcond) = ⊤
ract (refStAction refm gcond) = stAction
par (refStAction refm gcond) e sys = tt
gcondInd (refStAction refm gcond) e sys nsys (_ , cnd) gcnd = subst (λ z → gcond z) (sym cnd) gcnd
embed (refStAction refm gcond) e sys gcnd nsys (fst , refl)
  = tt , refl


refStAction′ : ∀{α n k} → {varsB : VSet {α} n} → {varsA : VSet {α} k}
              → (refm : System varsB → System varsA) → (gcond : GCond varsB) → RefAction refm gcond stAction′
RE (refStAction′ refm gcond) = ℓ↑ _ ⊤
ract (refStAction′ refm gcond) = stAction′
par (refStAction′ refm gcond) e sys = lift tt
gcondInd (refStAction′ refm gcond) e sys nsys (_ , cnd) gcnd = subst (λ z → gcond z) (sym cnd) gcnd 
embed (refStAction′ refm gcond) e sys gcnd nsys (fst , refl)
  = (lift tt) , refl



infixr 5 _∷ᵣₛₚ_
infixr 5 _m∷ᵣₛₚ_
data RSpec {α n k} {varsB : VSet {α} n} {varsA : VSet {α} k}
           (refm : System varsB → System varsA) (gcond : GCond varsB) : ∀{el bl} → {PB : VSet {α} bl} → (PE : VSet {α} el)
           → (spec : Spec varsA PB) → Set (lsuc α) where
  _m∷ᵣₛₚ_ : ∀{B act bl PB el PE spec} → (ref : RefAction {B = B} refm gcond act)
            → (rspec : RSpec refm gcond {el = el} {bl = suc bl} {PB = B ∷ PB} PE (act ∷ₛₚ spec))
            → RSpec refm gcond {PB = B ∷ PB} (RE ref ∷ PE) (act ∷ₛₚ spec)
  _∷ᵣₛₚ_ : ∀{B act bl PB el PE spec} → (ref : RefAction {B = B} refm gcond act)
           → (rspec : RSpec refm gcond {el = el} {bl = bl} {PB = PB} PE spec)
           → RSpec refm gcond {PB = B ∷ PB} (RE ref ∷ PE) (act ∷ₛₚ spec)
  []ᵣₛₚ : RSpec refm gcond [] []ₛₚ


exSpec : ∀{α lb la varsB varsA el PE bl PB spec} → {refm : System {α} {lb} varsB → System {α} {la} varsA}
         → {gcond : GCond varsB} → RSpec refm gcond {el = el} {bl = bl} {PB = PB} PE spec
         → Spec varsB PE
exSpec (ref m∷ᵣₛₚ rspec) = (ract ref) ∷ₛₚ (exSpec rspec)
exSpec (ref ∷ᵣₛₚ rspec) = (ract ref) ∷ₛₚ (exSpec rspec)
exSpec []ᵣₛₚ = []ₛₚ



exPar :  ∀{α lb la varsB varsA el PE bl PB spec} → {refm : System {α} {lb} varsB → System {α} {la} varsA}
         → {gcond : GCond varsB} → RSpec refm gcond {el = el} {bl = bl} {PB = PB} PE spec
         → (PE toUS) → (System varsB) → (PB toUS)
exPar (ref m∷ᵣₛₚ rspec) (e ←u) sys = par ref e sys ←u
exPar (ref m∷ᵣₛₚ rspec) (u→ pe) sys = exPar rspec pe sys
exPar (ref ∷ᵣₛₚ rspec) (e ←u) sys = par ref e sys ←u
exPar (ref ∷ᵣₛₚ rspec) (u→ pe) sys = u→ exPar rspec pe sys


refTh : ∀{α lb la varsB varsA el PE bl PB spec} → {refm : System {α} {lb} varsB → System {α} {la} varsA}
             → {gcond : GCond varsB} → (rspec : RSpec refm gcond {el = el} {bl = bl} {PB = PB} PE spec)
             → (sys nsys : (System varsB)) → (pe : (PE toUS)) → (gcnd : gcond sys)
             → (exSpec rspec  $ₛₚ pe) sys nsys → (spec $ₛₚ (exPar rspec pe sys)) (refm sys) (refm nsys)
refTh (ref m∷ᵣₛₚ rspec) sys nsys (e ←u) gcnd rst = embed ref e sys nsys gcnd rst
refTh (ref m∷ᵣₛₚ rspec) sys nsys (u→ pe) gcnds rst = refTh rspec sys nsys pe gcnds rst
refTh (ref ∷ᵣₛₚ rspec) sys nsys (e ←u) gcnd rst = embed ref e sys nsys gcnd rst
refTh (ref ∷ᵣₛₚ rspec) sys nsys (u→ pe) gcnds rst = refTh rspec sys nsys pe gcnds rst
refTh []ᵣₛₚ sys nsys () rst



trefTh : ∀{α lb la varsB varsA el PE bl PB spec} → {refm : System {α} {lb} varsB → System {α} {la} varsA}
             → {gcond : GCond varsB} → (rspec : RSpec refm gcond {el = el} {bl = bl} {PB = PB} PE spec)
             → (beh : (System varsB) ʷ) → (pe : (PE toUS) ʷ) → [ ⟨ gcond ⟩ $ beh ]
             → [ ((exSpec rspec  $ₛₚₜ pe) beh) ⇒ ((spec $ₛₚₜ (⟨ exPar rspec ⟩ $ pe $ beh) ) (⟨ refm ⟩ $ beh)) ]
trefTh rspec beh pe gcnd n rst = refTh rspec(beh n) (beh (suc n)) (pe n) (gcnd n) rst


rspec⇒gcond : ∀{α lb la varsB varsA el PE bl PB spec} → {refm : System {α} {lb} varsB → System {α} {la} varsA}
             → {gcond : GCond varsB} → (rspec : RSpec refm gcond {el = el} {bl = bl} {PB = PB} PE spec)
             → (sys nsys : (System varsB)) → (pe : (PE toUS))
             → (exSpec rspec  $ₛₚ pe) sys nsys → (gcnd : gcond sys) → gcond nsys
rspec⇒gcond (ref m∷ᵣₛₚ rspec) sys nsys (e ←u) rst gcnd = gcondInd ref e sys nsys rst gcnd
rspec⇒gcond (ref m∷ᵣₛₚ rspec) sys nsys (u→ pe) rst gcnd = rspec⇒gcond rspec sys nsys pe rst gcnd
rspec⇒gcond (ref ∷ᵣₛₚ rspec) sys nsys (e ←u) rst gcnd = gcondInd ref e sys nsys rst gcnd
rspec⇒gcond (ref ∷ᵣₛₚ rspec) sys nsys (u→ pe) rst gcnd =  rspec⇒gcond rspec sys nsys pe rst gcnd
rspec⇒gcond []ᵣₛₚ sys nsys (lift ()) rst gcnd


trspec⇒gcond : ∀{α lb la varsB varsA el PE bl PB spec} → {refm : System {α} {lb} varsB → System {α} {la} varsA}
             → {gcond : GCond varsB} → (rspec : RSpec refm gcond {el = el} {bl = bl} {PB = PB} PE spec)
             → (beh : (System varsB) ʷ) → (pe : (PE toUS) ʷ)
             → [ ((exSpec rspec  $ₛₚₜ pe) beh) ⇒ ⟨ gcond ⟩ $ beh ⇒ ⟨ gcond ⟩ $ (○ beh) ]
trspec⇒gcond rspec beh pe n rst ind = rspec⇒gcond rspec (beh n) (beh (suc n)) (pe n) rst ind
