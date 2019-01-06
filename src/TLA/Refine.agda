module TLA.Refine where

open import Level renaming (zero to lzero ; suc to lsuc ; Lift to ℓ↑)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat
open import Data.Unit
open import Data.Sum
open import Data.Bool
open import Data.List hiding (all)
open import Data.List.Membership.Propositional
open import Data.List.Any

open import LTL.Core renaming ([_] to [_]ₜ)
open import LTL.Stateless

open import TLA.Def
open import TLA.Utils

GCond : ∀{α} → (varsB : LSet {α}) → Set (lsuc α)
GCond {α} varsB = (sys : System varsB) → Set α

GCondV : ∀{α} → (varsB : LSet {α}) → Set (lsuc α)
GCondV {α} varsB = (sys : System varsB) → LSet {α}


-- Should we externalize RE ? It is used by RSpec already? Do we know RE before hand?
record RefAction {α}{varsB : LSet {α}} {varsA : LSet {α}} 
                 (refm : System varsB → System varsA)
                 (gcond : GCond varsB) (actB : Action varsB) (actA : Action varsA) : Set (lsuc α) where
  field
    par : (e : E actB) → (sys : System varsB) → E actA
    gcondInd : (e : E actB) → (sys : System varsB) → (nsys : System varsB)
               → (rst : cond actB e sys × resp actB e sys nsys) → (ind : gcond sys) → gcond nsys
    embed : (e : E actB) → (sys : System varsB) → (nsys : System varsB) → (gcnd : gcond sys)
            → (rst : cond actB e sys × resp actB e sys nsys)
            → (cond actA) (par e sys) (refm sys) × (resp actA) (par e sys) (refm sys) (refm nsys)
open RefAction public




refStAction : {varsB : LSet} → {varsA : LSet}
              → (refm : System varsB → System varsA) → (gcond : GCond varsB)
              → RefAction refm gcond stAction stAction
par (refStAction refm gcond) e sys = tt
gcondInd (refStAction refm gcond) e sys nsys (_ , cnd) gcnd = subst (λ z → gcond z) (sym cnd) gcnd
embed (refStAction refm gcond) e sys gcnd nsys (fst , refl)
  = tt , refl


refStAction′ : ∀{α} → {varsB : LSet {α}} → {varsA : LSet {α}}
              → (refm : System varsB → System varsA) → (gcond : GCond varsB)
              → RefAction refm gcond stAction′ stAction′
par (refStAction′ refm gcond) e sys = lift tt
gcondInd (refStAction′ refm gcond) e sys nsys (_ , cnd) gcnd = subst (λ z → gcond z) (sym cnd) gcnd 
embed (refStAction′ refm gcond) e sys gcnd nsys (fst , refl)
  = (lift tt) , refl

record RSAct {α} {varsB : LSet {α}} {varsA : LSet {α}}
            (refm : System varsB → System varsA)
            (gcond : GCond varsB) (actB : Action varsB) (specA : Spec varsA) : Set (lsuc α) where
  constructor rsa
  field
    actA : Action varsA
    bel : actA ∈ specA
    ref : RefAction refm gcond actB actA

open RSAct public

data RSpec {α} {varsB varsA : LSet {α}}
           (refm : System varsB → System varsA)
           (gcond : GCond varsB) (specA : Spec varsA)
           : (specB : Spec varsB) → Set (lsuc α) where
 _∷ᵣ_ : ∀{act spec} → RSAct refm gcond act specA → RSpec refm gcond specA spec → RSpec refm gcond specA (act ∷ spec)
 []ᵣ : RSpec refm gcond specA []



cpe : ∀{α varsA} → {act : Action {α} varsA} → {spec : Spec varsA} → act ∈ spec → E act → PE spec toUS
cpe (here refl) b = b ←u
cpe (there x) b = u→ (cpe x b)

exPar :  ∀{α varsB varsA specB specA} → {refm : System {α} varsB → System {α} varsA}
         → {gcond : GCond varsB} → (rspec : RSpec refm gcond specA specB)
         → (PE specB toUS) → (System varsB) → (PE specA toUS)
exPar []ᵣ (lift ()) sys
exPar (x ∷ᵣ rspec) (e ←u) sys = cpe (bel x) (par (ref x) e sys)
exPar (x ∷ᵣ rspec) (u→ pe) sys = exPar rspec pe sys

rcpe : ∀{α varsB varsA actB spec} → {refm : System {α} varsB → System {α} varsA}
             → {gcond : GCond varsB} → (ra : RSAct refm gcond actB spec)
             → (sys nsys : (System varsB)) → (e : E actB) → (gcnd : gcond sys)
             → cond actB e sys × resp actB e sys nsys → (spec $ₛₚ cpe (bel ra) (par (ref ra) e sys)) (refm sys) (refm nsys)
rcpe (rsa act (here refl) ref) sys nsys e gcnd rst = embed ref e sys nsys gcnd rst
rcpe (rsa act (there bel) ref) sys nsys e gcnd rst = rcpe (rsa act bel ref) sys nsys e gcnd rst

refTh : ∀{α varsB varsA specA specB} → {refm : System {α} varsB → System {α} varsA}
             → {gcond : GCond varsB} → (rspec : RSpec refm gcond specA specB)
             → (sys nsys : (System varsB)) → (pe : (PE specB toUS)) → (gcnd : gcond sys)
             → (specB  $ₛₚ pe) sys nsys → (specA $ₛₚ (exPar rspec pe sys)) (refm sys) (refm nsys)
refTh []ᵣ sys nsys (lift ()) gcnd rst
refTh (x ∷ᵣ rspec) sys nsys (e ←u) gcnd rst = rcpe x sys nsys e gcnd rst
refTh (x ∷ᵣ rspec) sys nsys (u→ pe) gcnd rst = refTh rspec sys nsys pe gcnd rst


trefTh : ∀{α varsB varsA specA specB} → {refm : System {α} varsB → System {α} varsA}
             → {gcond : GCond varsB} → (rspec : RSpec refm gcond specA specB)
             → (beh : (System varsB) ʷ) → (pe : (PE specB toUS) ʷ) → [ ⟨ gcond ⟩ $ beh ]ₜ
             → [ ((specB  $ₛₚₜ pe) beh) ⇒ ((specA $ₛₚₜ (⟨ exPar rspec ⟩ $ pe $ beh) ) (⟨ refm ⟩ $ beh)) ]ₜ
trefTh rspec beh pe gcnd n rst = refTh rspec(beh n) (beh (suc n)) (pe n) (gcnd n) rst


rspec⇒ind-gcond : ∀{α varsB varsA specA specB} → {refm : System {α} varsB → System {α} varsA}
             → {gcond : GCond varsB} → (rspec : RSpec refm gcond specA specB)
             → (sys nsys : (System varsB)) → (pe : (PE specB toUS))
             → (specB  $ₛₚ pe) sys nsys → (gcnd : gcond sys) → gcond nsys
rspec⇒ind-gcond []ᵣ sys nsys (lift ()) rst gcnd
rspec⇒ind-gcond (x ∷ᵣ rspec) sys nsys (e ←u) rst gcnd = gcondInd (ref x) e sys nsys rst gcnd
rspec⇒ind-gcond (x ∷ᵣ rspec) sys nsys (u→ pe) rst gcnd = rspec⇒ind-gcond rspec sys nsys pe rst gcnd


trspec⇒ind-gcond : ∀{α varsB varsA specA specB} → {refm : System {α} varsB → System {α} varsA}
             → {gcond : GCond varsB} → (rspec : RSpec refm gcond specA specB)
             → (beh : (System varsB) ʷ) → (pe : (PE specB toUS) ʷ)
             → [ ((specB  $ₛₚₜ pe) beh) ⇒ ⟨ gcond ⟩ $ beh ⇒ ⟨ gcond ⟩ $ (○ beh) ]ₜ
trspec⇒ind-gcond rspec beh pe n rst ind = rspec⇒ind-gcond rspec (beh n) (beh (suc n)) (pe n) rst ind


trspec⇒gcond : ∀{α varsB varsA specA specB} → {refm : System {α} varsB → System {α} varsA}
            → {gcond : GCond varsB} → (rspec : RSpec refm gcond specA specB)
            → (beh : (System varsB) ʷ) → (pe : (PE specB toUS) ʷ) → gcond (! beh)
            → [ ((specB  $ₛₚₜ pe) beh) ]ₜ → [ ⟨ gcond ⟩ $ beh ]ₜ
trspec⇒gcond rspec beh pe init rst = indn (trspec⇒ind-gcond rspec beh pe $ rst) init




-- This type of refinement does not require the knowledge of initial conditions.
record Ref {α} {varsB varsA : LSet {α}}
           (refm : System varsB → System varsA)
           (specB : Spec varsB)
           (specA : Spec varsA) : Set (lsuc α) where
  field
    rspec : RSpec refm (λ sys → ℓ↑ _ ⊤) specA specB
  
-- Keep in mind that if we order the speciB according to the initial condition,
-- then the element with init ≡ gcond is the maximal one with regards to this specific proof RSPec.
record RefI {α} {varsB varsA : LSet {α}}
           (refm : System varsB → System varsA)
           (speciB : SpecI varsB)
           (speciA : SpecI varsA) : Set (lsuc α) where
  open SpecI
  field
    gcond : GCond varsB
    icond : ∀ sys → (init speciB) sys → (init speciA) (refm sys)
    igcond : ∀ sys → (init speciB) sys → gcond sys
    rspec : RSpec refm gcond (spec speciA) (spec speciB)


-- Simpler version . Here we have the maximal element for this proof (RSpec)
-- We assume that the initial elements respect the global condition.
record RefG {α} {varsB varsA : LSet {α}}
           (refm : System varsB → System varsA)
           (specB : Spec varsB)
           (specA : Spec varsA) : Set (lsuc α) where
  open SpecI
  field
    gcond : GCond varsB
    rspec : RSpec refm gcond specA specB


-- Even though Refs do prove GRef due to the refinement theorem refth, composition is not easy
-- for these Refs. On the other hand, Composition is possible for GRef.
Tcnd : ∀{α} → (vars : LSet {α}) → Set (lsuc α)
Tcnd {α} vars = (beh : (System vars) ʷ) → Set α

GRef : ∀{α} {varsB varsA : LSet {α}}
            (refm : System varsB → System varsA)
            (tcndB : Tcnd varsB) (tcndA : Tcnd varsA) → Set α 
GRef refm tcndB tcndA = ∀ beh → tcndB beh → tcndA (⟨ refm ⟩ $ beh)
