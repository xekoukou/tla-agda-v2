module TLA.Def2 where

open import Prelude.Vec public
open import Prelude.Unit public
open import Prelude.Nat public
open import Prelude.Empty public
open import Prelude.Product public
open import Prelude.Decidable public
open import Prelude.Sum renaming (Either to _⊎_) public
open import Prelude.Functor public
open import Prelude.Equality public
open import Prelude.Maybe public
open import Prelude.List public hiding ([_])

open import LTL.Core public
open import LTL.Sum public
open import LTL.Stateless public

open import Agda.Primitive public


variable
  α β : Level
  n k m : Nat
  A : Set _
  B : Set _
  C : Set _
  D : Set _
  E : Set _



postulate IMPOSSIBLE : A


PSet : (n : Nat) → Set (lsuc α)
PSet {α} n = Vec (Set α) n


VSet : (n : Nat) → Set (lsuc α)
VSet n = PSet (suc n)

pattern _×ₚ_ B PB = Vec._∷_ B PB
pattern _⊎⊥ B = Vec._∷_ B Vec.[]
pattern ⊤ₚ = Vec.[]


pStoS : PSet {α} n → Set α
pStoS (S ×ₚ pd) = S × pStoS pd
pStoS ⊤ₚ = ⊤′


pStoUS : PSet {α} n → Set α
pStoUS ⊤ₚ = ⊤′
pStoUS (S ×ₚ pd) = S ⊎ (pStoUS pd)


pattern u→_ a = right a
pattern _←u a = left a

-- Is this needed?
_toMPSet : PSet {α} n → PSet {α} n
(B ×ₚ pset) toMPSet = Maybe B ×ₚ (pset toMPSet)
⊤ₑ toMPSet = ⊤ₑ



variable
  vars varsA varsB : VSet _
  PA PB PC PD PE : PSet _



u→∅ : pStoUS PB
u→∅ {PB = ⊤ₚ} = unit
u→∅ {PB = B ×ₚ PB} = u→ u→∅ 


-- Non Termporal so as to be used by Actions.
System : VSet {α} n → Set α
System (B ×ₚ PB@(_ ×ₚ _)) = B × System PB
System (B ⊎⊥) = B


variable
  sys nsys sysA sysB :  System _


record Action {α n} (vars : VSet {α} n) : Set (lsuc α) where
  field
    cond : (sys : System vars) → Set α
    resp : (sys : System vars) → (nsys : System vars) → Set α

open Action public


PAction : (B : Set α) → (vars : VSet {α} n) → Set (lsuc α)
PAction B vars = B → Action vars 


variable
  act actA actB : Action _
  pact pactA pactB : PAction _ _




record ConAction {α n} {vars : VSet {α} n} (act : Action vars) : Set (lsuc α) where
  field
    impl : (sys : System vars) → (cnd : (cond act) sys) → ∃ (λ nsys → resp act sys nsys)
open ConAction public

simpleAction : ConAction {vars = vars} act → (sys : System vars) → (cnd : (cond act) sys) → System vars
simpleAction cact sys cnd = fst (impl cact sys cnd)

record ConPAction {α n} {vars : VSet {α} n} {B : Set α} (pact : PAction B vars) : Set (lsuc α) where
  field
    par : System vars → B
    impl : (sys : System vars) → (cnd : (cond (pact (par sys))) sys) → ∃ (λ nsys → resp (pact (par sys)) sys nsys)
open ConPAction public


simplePAction : (cn : ConPAction {vars = vars} pact) → ((sys : System vars) → (cond (pact (par cn sys))) sys → System vars)
simplePAction cact sys cnd = fst ((impl cact) sys cnd)



Spec : (vars : VSet {α} n) → Set (lsuc α)
Spec vars = List (Action vars)


data PSpec {α n} (vars : VSet {α} n) : ∀{k} → (PB : PSet {α} k) → Set (lsuc α) where
  _+psp+_ : (pact : PAction B vars) → (pspec : PSpec vars PB) → PSpec vars (B ×ₚ PB)
  psp∅ : PSpec vars ⊤ₚ


record GSpec {α n k} (vars : VSet {α} n) (PB : PSet {α} k) : Set (lsuc α) where
  constructor gsp
  field
    sp : Spec vars
    psp : PSpec vars PB


open GSpec public

variable
  pspec pspecA pspecB : PSpec _ _
  spec specA specB : Spec _
  gspec gspecA gspecB : GSpec _ _
  beh behA behB :  (System _) ʷ



-- Implementation of some Actions
-- PSpec is assumed to be a subset of a PSpec.
-- TODO How do we split a PSpec and how do we compose Specs?
ConPSpec : (spec : PSpec {α} vars PB) → Set (lsuc α)
ConPSpec (pact +psp+ spec) = ConPAction pact × ConPSpec spec
ConPSpec s∅ = ⊤′


ConSpec : (spec : Spec {α} vars) → Set (lsuc α)
ConSpec [] = ⊤′
ConSpec (act ∷ spec) = ConAction act × ConSpec spec

ConGSpec : (gspec : GSpec {α} vars PB) → Set (lsuc α)
ConGSpec gspec = ConSpec (sp gspec) × ConPSpec (psp gspec)





_$ᵖˢ_ : (pspec : PSpec vars PB) → (b : pStoUS PB) → List (Action vars)
(pact +psp+ spec) $ᵖˢ (b ←u) = pact b ∷ []
(pact +psp+ spec) $ᵖˢ (u→ b) = spec $ᵖˢ b
psp∅ $ᵖˢ b = []

_$ᵍˢ_ : (spec : GSpec vars PB) → (b : pStoUS PB) → Spec vars
gspec $ᵍˢ b = ((psp gspec) $ᵖˢ b) ++ (sp gspec)


PrConds : (spec : Spec {α} vars) → (sys : System vars) → Set α
PrConds [] sys = ⊤′
PrConds (act ∷ spec) sys = Dec (cond act sys) × PrConds spec sys

UnResp : (spec : Spec {α} vars) → (sys : System vars) → (nsys : System vars) → (pCnds : PrConds spec sys) → Set α
UnResp [] sys nsys pCnds = ⊥′
UnResp (act ∷ spec) sys nsys (yes x , pcnds) = resp act sys nsys ⊎ UnResp spec sys nsys pcnds
UnResp (act ∷ spec) sys nsys (no x , pcnds) = UnResp spec sys nsys pcnds



Restr : (spec : Spec {α} vars) → (sys : System vars) → (nsys : System vars)
        → (pcnds : PrConds spec sys) → Set α
Restr spec sys nsys pcnds = UnResp spec sys nsys pcnds


Stut : (sys : System {α} vars) → (System {α} vars) → Set α
Stut sys nsys = sys ≡ nsys

RestrWithSt : (spec : Spec {α} vars) → (sys : System vars) → (nsys : System vars)
              → (pcnds : PrConds spec sys) → Set α
RestrWithSt {vars = vars} spec sys nsys pcnds = Restr spec sys nsys pcnds ⊎ Stut {vars = vars} sys nsys

TRestr : (spec : Spec {α} vars) → (beh : (System vars) ʷ)
         → (pcnds : [ ⟨ PrConds spec ⟩ $ʷ beh ]) → (Set α) ʷ
TRestr spec beh pcnds = (⟨ Restr spec ⟩ $ʷ beh $ʷ (○ beh) $ʷ pcnds)

TStut : (beh : (System {α} vars) ʷ) → (Set α) ʷ
TStut {vars = vars} beh = ⟨ Stut {vars = vars} ⟩ $ʷ beh $ʷ (○ beh)

TRestrWithSt : (spec : Spec {α} vars) → (beh : (System vars) ʷ)
               → (pcnds : [ ⟨ PrConds spec ⟩ $ʷ beh ]) → (Set α) ʷ
TRestrWithSt {vars = vars} spec beh pcnds = TRestr spec beh pcnds ∨ TStut {vars = vars} beh


-- MPAction is a PAction that takes Maybe B as input.
-- This is necessary because we will not always have a B.
-- The presence of B is determined by the action taken at time t.
-- TODO Probably not required ?
MPAction : (B : Set α) → (vars : VSet {α} n) → Set (lsuc α)
MPAction B vars = Maybe B → Action vars


⊥-Action : Action vars
cond ⊥-Action sys = ⊥′
resp ⊥-Action sys nsys = ⊥′

-- Not required.
_toMPAction : PAction B vars → MPAction B vars
(pa toMPAction) nothing  = ⊥-Action
(pa toMPAction) (just x) = pa x



-- To restrict the general case of specification, we need to lift all PActions into
-- MActions.
-- Not required
_toMPSpec : PSpec vars PB → PSpec vars (PB toMPSet)
(pact +psp+ pspec) toMPSpec = (pact toMPAction) +psp+ (pspec toMPSpec)
psp∅ toMPSpec = psp∅


-- Not required
_toMGSpec : GSpec vars PB → GSpec vars (PB toMPSet)
sp (gspec toMGSpec) = sp gspec
psp (gspec toMGSpec) = (psp gspec) toMPSpec


-- These might not be neccessary

-- PRestr : (pspec : PSpec {α} vars PB) → (sys : System vars) → (nsys : System vars) → pStoUS PB → Set α
-- PRestr pspec sys nsys mpb = Restr (pspec $ᵖˢ mpb) sys nsys


-- TPRestr : (pspec : PSpec {α} vars PB) → (beh : (System vars) ʷ)
--           → (tmpb : ( pStoUS PB ) ʷ) → (Set α ) ʷ
-- TPRestr pspec beh tmpb = ⟨ Restr ⟩ $ʷ (⟨ pspec $ᵖˢ_ ⟩ $ʷ tmpb) $ʷ beh $ʷ ○ beh

-- -- Instead of defining a GRestr, we first apply b at gspec which results in a spec, and then we can have the
-- -- standard restriction of the spec. (Restr and RestrWithSt)
