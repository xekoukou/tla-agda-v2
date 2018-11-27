module TLA.Refine where

open import Level renaming (zero to lzero ; suc to lsuc ; Lift to ℓ↑)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat
open import Data.Sum
open import Data.Vec hiding ([_] ; split)

open import LTL.Core
open import LTL.Stateless

open import TLA.Def
open import TLA.Utils



record RefAction {α n k}{varsB : VSet {α} k} {varsA : VSet {α} n} 
                 {B : Set α} (refm : System varsB → System varsA) (actA : Action B varsA) : Set (lsuc α) where
  field
    RE : Set α
    ract : Action RE varsB
    par : (e : RE) → (sys : System varsB) → B
    gcond : (sys : System varsB) → Set α
    embed : (e : RE) → (sys : System varsB) → (gcnd : gcond sys) → (nsys : System varsB)
            → cond ract e sys × resp ract e sys nsys
            → (cond actA) (par e sys) (refm sys) × (resp actA) (par e sys) (refm sys) (refm nsys)
open RefAction public


record RefStAction {α n k}{varsB : VSet {α} k} {varsA : VSet {α} n} 
                   (refm : System varsB → System varsA) : Set (lsuc α) where
  field
    RE : Set α
    ract : Action RE varsB
    isConst : (e : RE) → (sys : System varsB) → (nsys : System varsB)
            → cond ract e sys × resp ract e sys nsys
            → refm sys ≡ refm nsys all
open RefStAction public


variable
  la lb : ℕ
  varsB : VSet {α} lb
  varsA : VSet {α} la
  refm : System varsB → System varsA

data RSpec {α n} {varsB : VSet {α} n} {varsA : VSet {α} n}
           (refm : System varsB → System varsA) : ∀{el bl} → {PB : VSet {α} bl} → (PE : VSet {α} el)
           → (spec : Spec varsA PB) → Set (lsuc α) where
  _m∷ᵣₛₚ_ : (ref : RefAction {varsB = varsB} {varsA = varsA} {B = B} refm act)
            → (rspec : RSpec {varsB = varsB} {varsA = varsA} refm {PB = B ∷ PB} PE (act ∷ₛₚ spec)) → RSpec refm {PB = B ∷ PB} (RE ref ∷ PE) (act ∷ₛₚ spec)
  _∷ᵣₛₚ_ : (ref : RefAction {varsB = varsB} {varsA = varsA} {B = B} refm act)
           → (rspec : RSpec {varsB = varsB} {varsA = varsA} refm {PB = PB} PE spec) → RSpec refm {PB = B ∷ PB} (RE ref ∷ PE) (act ∷ₛₚ spec)
  []ᵣₛₚ : RSpec refm [] []ₛₚ

data RSpecSt {α n} {varsB : VSet {α} n} {varsA : VSet {α} n}
           (refm : System varsB → System varsA) : ∀{el} → (PE : VSet {α} el)
           → Set (lsuc α) where
  _∷ᵣₛₜ_ : (ref : RefStAction {varsB = varsB} {varsA = varsA} refm)
           → (rspec : RSpecSt {varsB = varsB} {varsA = varsA} refm PE) → RSpecSt refm (RE ref ∷ PE)
  []ᵣₛₜ : RSpecSt refm []


exSpec : {refm : System varsB → System varsA} → RSpec {varsB = varsB} {varsA = varsA} refm PE spec
              → Spec varsB PE
exSpec (ref m∷ᵣₛₚ rspec) = (ract ref) ∷ₛₚ (exSpec rspec)
exSpec (ref ∷ᵣₛₚ rspec) = (ract ref) ∷ₛₚ (exSpec rspec)
exSpec []ᵣₛₚ = []ₛₚ

exGcond : {refm : System varsB → System varsA} → RSpec {α = α} {varsB = varsB} {varsA = varsA} refm {el = el} PE spec
          → (sys : System varsB) → VSet {α} el
exGcond (ref m∷ᵣₛₚ rspec) sys = gcond ref sys ∷ exGcond rspec sys
exGcond (ref ∷ᵣₛₚ rspec) sys = gcond ref sys ∷ exGcond rspec sys
exGcond []ᵣₛₚ sys = []

exSpecSt : {refm : System varsB → System varsA} → RSpecSt {varsB = varsB} {varsA = varsA} refm PE
              → Spec varsB PE
exSpecSt (ref ∷ᵣₛₜ rspec) = (ract ref) ∷ₛₚ (exSpecSt rspec)
exSpecSt []ᵣₛₜ = []ₛₚ


exPar : {refm : System varsB → System varsA}
             → (rspec : RSpec {varsB = varsB} {varsA = varsA} refm {PB = PB} PE spec)
             → (PE toUS) → (System varsB) → (PB toUS)
exPar (ref m∷ᵣₛₚ rspec) (e ←u) sys = par ref e sys ←u
exPar (ref m∷ᵣₛₚ rspec) (u→ pe) sys = exPar rspec pe sys
exPar (ref ∷ᵣₛₚ rspec) (e ←u) sys = par ref e sys ←u
exPar (ref ∷ᵣₛₚ rspec) (u→ pe) sys = u→ exPar rspec pe sys




refTheorem : {refm : System varsB → System varsA}
             → (rspec : RSpec {varsB = varsB} {varsA = varsA} refm {PB = PB} PE spec)
              → (sys nsys : (System varsB)) → (pe : (PE toUS)) → exGcond rspec sys toPS
             → (exSpec rspec  $ₛₚ pe) sys nsys → (spec $ₛₚ (exPar rspec pe sys)) (refm sys) (refm nsys)
refTheorem (ref m∷ᵣₛₚ rspec) sys nsys (e ←u) (gcnd , gcnds) rst = embed ref e sys gcnd nsys rst
refTheorem (ref m∷ᵣₛₚ rspec) sys nsys (u→ pe) (gcnd , gcnds) rst = refTheorem rspec sys nsys pe gcnds rst
refTheorem (ref ∷ᵣₛₚ rspec) sys nsys (e ←u) (gcnd , gcnds) rst = embed ref e sys gcnd nsys rst
refTheorem (ref ∷ᵣₛₚ rspec) sys nsys (u→ pe) (gcnd , gcnds) rst = refTheorem rspec sys nsys pe gcnds rst
refTheorem []ᵣₛₚ sys nsys () rst



trefTheorem : {refm : System varsB → System varsA}
             → (rspec : RSpec {varsB = varsB} {varsA = varsA} refm {PB = PB} PE spec)
             → (beh : (System varsB) ʷ) → (pe : (PE toUS) ʷ) → [ ⟨ (λ sys → exGcond rspec sys toPS ) ⟩ $ beh ]
             → [ ((exSpec rspec  $ₛₚₜ pe) beh) ⇒ ((spec $ₛₚₜ (⟨ exPar rspec ⟩ $ pe $ beh) ) (⟨ refm ⟩ $ beh)) ]
trefTheorem rspec beh pe gcnd n rst = refTheorem rspec(beh n) (beh (suc n)) (pe n) (gcnd n) rst


refTheoremSt : {refm : System varsB → System varsA}
             → (rspec : RSpecSt {varsB = varsB} {varsA = varsA} refm PE)
              → (sys nsys : (System varsB)) → (pe : (PE toUS))
             → (exSpecSt rspec $ₛₚ pe) sys nsys → Stut {vars = varsA} (refm sys) (refm nsys)
refTheoremSt (ref ∷ᵣₛₜ rspec) sys nsys (e ←u) rst = isConst ref e sys nsys rst
refTheoremSt (ref ∷ᵣₛₜ rspec) sys nsys (u→ pe) rst = refTheoremSt rspec sys nsys pe rst
refTheoremSt []ᵣₛₜ sys nsys () rst


trefTheoremSt : {refm : System varsB → System varsA}
             → (rspec : RSpecSt {varsB = varsB} {varsA = varsA} refm PE)
              → (beh : (System varsB) ʷ) → (pe : (PE toUS) ʷ)
             → [ (exSpecSt rspec $ₛₚₜ pe) beh ⇒ TStut {vars = varsA} (⟨ refm ⟩ $ beh) ]
trefTheoremSt rspec beh pe n x = refTheoremSt rspec (beh n) (beh (suc n)) (pe n) x


GRestr : {PE : VSet {α} el} → {PB : VSet {α} bl} → {PEST : VSet {α} esl} → {spec : Spec varsA PB}
         → {refm : System varsB → System varsA}
  → (rspec : RSpec {varsB = varsB} {varsA = varsA} refm {PB = PB} PE spec)
  → (rspecSt : RSpecSt {varsB = varsB} {varsA = varsA} refm PEST )
  → (sys nsys : (System varsB)) → (pe : ((PE ++ PEST) toUS))
  → Set α
GRestr {varsB = varsB} {varsA = varsA} {PE} {PB} {PEST} {spec = spec} {refm} rspec rspecSt sys nsys pe
  = ([_,_] (λ pe → (exSpec rspec  $ₛₚ pe) sys nsys
                   → (spec $ₛₚ (exPar rspec pe sys)) (refm sys) (refm nsys) )
           (λ pe → (exSpecSt rspecSt $ₛₚ pe) sys nsys
                   → Stut {vars = varsA} (refm sys) (refm nsys))
    ) (split PE PEST pe)
    


GRefTheorem : {refm : System varsB → System varsA}
  → (rspec : RSpec {varsB = varsB} {varsA = varsA} refm {PB = PB} PE spec)
  → (rspecSt : RSpecSt {varsB = varsB} {varsA = varsA} refm PEST )
  → (sys nsys : (System varsB)) → (pe : ((PE ++ PEST) toUS)) → exGcond rspec sys toPS 
  → GRestr rspec rspecSt sys nsys pe
GRefTheorem {PE = PE} {PEST = PEST} rspec rspecSt sys nsys pe gcnd with split PE PEST pe
GRefTheorem {PE = PE} {PEST = PEST} rspec rspecSt sys nsys pe gcnd | x ←u
  = refTheorem rspec sys nsys x gcnd
GRefTheorem {PE = PE} {PEST = PEST} rspec rspecSt sys nsys pe gcnd | u→_ x
  = refTheoremSt rspecSt sys nsys x



TGRefTheorem : {refm : System varsB → System varsA}
  → (rspec : RSpec {varsB = varsB} {varsA = varsA} refm {PB = PB} PE spec)
  → (rspecSt : RSpecSt {varsB = varsB} {varsA = varsA} refm PEST )
  → (beh : (System varsB) ʷ) → (pe : ((PE ++ PEST) toUS) ʷ) → [ ⟨ (λ sys → exGcond rspec sys toPS ) ⟩ $ beh ]
  → [ ⟨ GRestr rspec rspecSt ⟩ $ beh $ ○ beh $ pe ]
TGRefTheorem rspec rspecSt beh pe gcnd n = GRefTheorem rspec rspecSt (beh n) (beh (suc n)) (pe n) (gcnd n)

