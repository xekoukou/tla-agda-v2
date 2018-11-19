module TLA.Refine3 where

open import TLA.Def3



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
  _∷ᵣₛₚ_ : (ref : RefAction {varsB = varsB} {varsA = varsA} {B = B} refm act)
           → (rspec : RSpec {varsB = varsB} {varsA = varsA} refm {PB = PB} PE spec) → RSpec refm {PB = B ∷ PB} (RE ref ∷ PE) (act ∷ₛₚ spec)
  _ᵣ■ : (ref : RefAction {varsB = varsB} {varsA = varsA} {B = B} refm act) → RSpec refm {PB = B ∷ []} (RE ref ∷ []) (act ■)

data RSpecSt {α n} {varsB : VSet {α} n} {varsA : VSet {α} n}
           (refm : System varsB → System varsA) : ∀{el} → (PE : VSet {α} el)
           → Set (lsuc α) where
  _∷ᵣₛₜ_ : (ref : RefStAction {varsB = varsB} {varsA = varsA} refm)
           → (rspec : RSpecSt {varsB = varsB} {varsA = varsA} refm PE) → RSpecSt refm (RE ref ∷ PE)
  _ᵣₛₜ■ : (ref : RefStAction {varsB = varsB} {varsA = varsA} refm) → RSpecSt refm (RE ref ∷ [])



exSpec : {refm : System varsB → System varsA} → RSpec {varsB = varsB} {varsA = varsA} refm PE spec
              → Spec varsB PE
exSpec (ref ∷ᵣₛₚ rspec) = (ract ref) ∷ₛₚ (exSpec rspec)
exSpec (ref ᵣ■) = (ract ref) ■

exSpecSt : {refm : System varsB → System varsA} → RSpecSt {varsB = varsB} {varsA = varsA} refm PE
              → Spec varsB PE
exSpecSt (ref ∷ᵣₛₜ rspec) = (ract ref) ∷ₛₚ (exSpecSt rspec)
exSpecSt (ref ᵣₛₜ■) = (ract ref) ■


exPar : {refm : System varsB → System varsA}
             → (rspec : RSpec {varsB = varsB} {varsA = varsA} refm {PB = PB} PE spec)
             → (PE toUS) → (System varsB) → (PB toUS)
exPar {PE = .(RE ref) ∷ []} (ref ᵣ■) pe beh = par ref pe beh
exPar {PE = .(RE ref) ∷ _ ∷ _} (ref ∷ᵣₛₚ rspec@(_ ∷ᵣₛₚ _)) (_←u e) beh = par ref e beh ←u
exPar {PE = .(RE ref) ∷ _ ∷ _} (ref ∷ᵣₛₚ rspec@(_ ᵣ■)) (e ←u) beh = par ref e beh ←u
exPar {PE = .(RE ref) ∷ _ ∷ _} (ref ∷ᵣₛₚ rspec@(_ ∷ᵣₛₚ _)) (u→ pe) beh = u→ exPar rspec pe beh
exPar {PE = .(RE ref) ∷ _ ∷ _} (ref ∷ᵣₛₚ rspec@(_ ᵣ■)) (u→ pe) beh = u→ exPar rspec pe beh


refTheorem : {refm : System varsB → System varsA}
             → (rspec : RSpec {varsB = varsB} {varsA = varsA} refm {PB = PB} PE spec)
              → (sys nsys : (System varsB)) → (pe : (PE toUS))
             → (< PE > exSpec rspec  $ pe) sys nsys → (< PB > spec $ (exPar rspec pe sys)) (refm sys) (refm nsys)
refTheorem (ref ∷ᵣₛₚ (_ ∷ᵣₛₚ _)) sys nsys (e ←u) rst = embed ref e sys nsys rst
refTheorem (ref ∷ᵣₛₚ rspec@(_ ∷ᵣₛₚ _)) sys nsys (u→ pe) rst = refTheorem rspec sys nsys pe rst
refTheorem (ref ∷ᵣₛₚ (_ ᵣ■)) sys nsys (e ←u ) rst = embed ref e sys nsys rst
refTheorem (_ ∷ᵣₛₚ (ref ᵣ■)) sys nsys (u→ pe) rst = embed ref pe sys nsys rst
refTheorem (ref ᵣ■) sys nsys pe rst = embed ref pe sys nsys rst


trefTheorem : {refm : System varsB → System varsA}
             → (rspec : RSpec {varsB = varsB} {varsA = varsA} refm {PB = PB} PE spec)
             → (beh : (System varsB) ʷ) → (pe : (PE toUS) ʷ)
             → [ ((< PE > exSpec rspec  $ₜ pe) beh) ⇒ ((< PB > spec $ₜ (⟨ exPar rspec ⟩ $ʷ pe $ʷ beh) ) (⟨ refm ⟩ $ʷ beh)) ]
trefTheorem rspec beh pe n rst = refTheorem rspec(beh n) (beh (suc n)) (pe n) rst


refTheoremSt : {refm : System varsB → System varsA}
             → (rspec : RSpecSt {varsB = varsB} {varsA = varsA} refm PE)
              → (sys nsys : (System varsB)) → (pe : (PE toUS))
             → (< PE > exSpecSt rspec $ pe) sys nsys → Stut {vars = varsA} (refm sys) (refm nsys)
refTheoremSt (ref ∷ᵣₛₜ rspec@(_ ∷ᵣₛₜ _)) sys nsys (e ←u) rst = isConst ref e sys nsys rst
refTheoremSt (ref ∷ᵣₛₜ rspec@(_ ∷ᵣₛₜ _)) sys nsys (u→ pe) rst = refTheoremSt rspec sys nsys pe rst
refTheoremSt (ref ∷ᵣₛₜ (_ ᵣₛₜ■)) sys nsys (e ←u) rst = isConst ref e sys nsys rst
refTheoremSt (_ ∷ᵣₛₜ (ref ᵣₛₜ■)) sys nsys (u→ pe) rst = isConst ref pe sys nsys rst
refTheoremSt (ref ᵣₛₜ■) sys nsys pe rst = isConst ref pe sys nsys rst


trefTheoremSt : {refm : System varsB → System varsA}
             → (rspec : RSpecSt {varsB = varsB} {varsA = varsA} refm PE)
              → (beh : (System varsB) ʷ) → (pe : (PE toUS) ʷ)
             → [ (< PE > exSpecSt rspec $ₜ pe) beh ⇒ TStut {vars = varsA} (⟨ refm ⟩ $ʷ beh) ]
trefTheoremSt rspec beh pe n x = refTheoremSt rspec (beh n) (beh (suc n)) (pe n) x




gRefTheorem : {refm : System varsB → System varsA}
  → (rspec : RSpec {varsB = varsB} {varsA = varsA} refm {PB = PB} PE spec)
  → (rspecSt : RSpecSt {varsB = varsB} {varsA = varsA} refm PEST )
  → (sys nsys : (System varsB)) → (pe : ((PE v++ PEST) toUS))
  → either (λ pe → (< PE > exSpec rspec  $ pe) sys nsys
                   → (< PB > spec $ (exPar rspec pe sys)) (refm sys) (refm nsys) )
           (λ pe → (< PEST > exSpecSt rspecSt $ pe) sys nsys → Stut {vars = varsA} (refm sys) (refm nsys))
           (split PE PEST pe)
gRefTheorem {PE = PE} {PEST = PEST} rspec rspecSt sys nsys pe with split PE PEST pe
gRefTheorem {PE = PE} {PEST = PEST} rspec rspecSt sys nsys pe | x ←u
  = refTheorem rspec sys nsys x
gRefTheorem {PE = PE} {PEST = PEST} rspec rspecSt sys nsys pe | u→_ x
  = refTheoremSt rspecSt sys nsys x


