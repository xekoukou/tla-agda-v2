module TLA.Refine where

open import TLA.Def



record RefAction {α n k}{varsB : VSet {α} k} {varsA : VSet {α} n} 
                 {B : Set α} (refm : System varsB → System varsA) (actA : Action B varsA) : Set (lsuc α) where
  field
    RE : Set α
    ract : Action RE varsB
    par : RE → System varsB → B
    embed : (e : RE) → (vs : System varsB) → (nvs : System varsB)
            → cond ract e vs × resp ract e vs nvs
            → (cond actA) (par e vs) (refm vs) × (resp actA) (par e vs) (refm vs) (refm nvs)
open RefAction public


record RefStAction {α n k}{varsB : VSet {α} k} {varsA : VSet {α} n} 
                   (refm : System varsB → System varsA) : Set (lsuc α) where
  field
    RE : Set α
    ract : Action RE varsB
    isConst : (e : RE) → (vs : System varsB) → (nvs : System varsB)
            → cond ract e vs × resp ract e vs nvs
            → refm vs ≡ refm nvs
open RefStAction public


variable
  la lb : Nat
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
              → (sys nsys : (System varsB)) → (pe : (PE toUS))
             → (exSpec rspec  $ₛₚ pe) sys nsys → (spec $ₛₚ (exPar rspec pe sys)) (refm sys) (refm nsys)
refTheorem (ref m∷ᵣₛₚ rspec) sys nsys (e ←u) rst = embed ref e sys nsys rst
refTheorem (ref m∷ᵣₛₚ rspec) sys nsys (u→ pe) rst = refTheorem rspec sys nsys pe rst
refTheorem (ref ∷ᵣₛₚ rspec) sys nsys (e ←u) rst = embed ref e sys nsys rst
refTheorem (ref ∷ᵣₛₚ rspec) sys nsys (u→ pe) rst = refTheorem rspec sys nsys pe rst
refTheorem []ᵣₛₚ sys nsys () rst



trefTheorem : {refm : System varsB → System varsA}
             → (rspec : RSpec {varsB = varsB} {varsA = varsA} refm {PB = PB} PE spec)
             → (beh : (System varsB) ʷ) → (pe : (PE toUS) ʷ)
             → [ ((exSpec rspec  $ₛₚₜ pe) beh) ⇒ ((spec $ₛₚₜ (⟨ exPar rspec ⟩ $ʷ pe $ʷ beh) ) (⟨ refm ⟩ $ʷ beh)) ]
trefTheorem rspec beh pe n rst = refTheorem rspec(beh n) (beh (suc n)) (pe n) rst


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
             → [ (exSpecSt rspec $ₛₚₜ pe) beh ⇒ TStut {vars = varsA} (⟨ refm ⟩ $ʷ beh) ]
trefTheoremSt rspec beh pe n x = refTheoremSt rspec (beh n) (beh (suc n)) (pe n) x


GRestr : {PE : VSet {α} el} → {PB : VSet {α} bl} → {PEST : VSet {α} esl} → {spec : Spec varsA PB}
         → {refm : System varsB → System varsA}
  → (rspec : RSpec {varsB = varsB} {varsA = varsA} refm {PB = PB} PE spec)
  → (rspecSt : RSpecSt {varsB = varsB} {varsA = varsA} refm PEST )
  → (sys nsys : (System varsB)) → (pe : ((PE v++ PEST) toUS))
  → Set α
GRestr {varsB = varsB} {varsA = varsA} {PE} {PB} {PEST} {spec = spec} {refm} rspec rspecSt sys nsys pe
  = either (λ pe → (exSpec rspec  $ₛₚ pe) sys nsys
                   → (spec $ₛₚ (exPar rspec pe sys)) (refm sys) (refm nsys) )
           (λ pe → (exSpecSt rspecSt $ₛₚ pe) sys nsys
                   → Stut {vars = varsA} (refm sys) (refm nsys))
           (split PE PEST pe)

GRefTheorem : {refm : System varsB → System varsA}
  → (rspec : RSpec {varsB = varsB} {varsA = varsA} refm {PB = PB} PE spec)
  → (rspecSt : RSpecSt {varsB = varsB} {varsA = varsA} refm PEST )
  → (sys nsys : (System varsB)) → (pe : ((PE v++ PEST) toUS))
  → GRestr rspec rspecSt sys nsys pe
GRefTheorem {PE = PE} {PEST = PEST} rspec rspecSt sys nsys pe with split PE PEST pe
GRefTheorem {PE = PE} {PEST = PEST} rspec rspecSt sys nsys pe | x ←u
  = refTheorem rspec sys nsys x
GRefTheorem {PE = PE} {PEST = PEST} rspec rspecSt sys nsys pe | u→_ x
  = refTheoremSt rspecSt sys nsys x



TGRefTheorem : {refm : System varsB → System varsA}
  → (rspec : RSpec {varsB = varsB} {varsA = varsA} refm {PB = PB} PE spec)
  → (rspecSt : RSpecSt {varsB = varsB} {varsA = varsA} refm PEST )
  → (beh : (System varsB) ʷ) → (pe : ((PE v++ PEST) toUS) ʷ)
  → [ ⟨ GRestr rspec rspecSt ⟩ $ʷ beh $ʷ ○ beh $ʷ pe ]
TGRefTheorem rspec rspecSt beh pe n = GRefTheorem rspec rspecSt (beh n) (beh (suc n)) (pe n)

