module TLA.Refine2 where

open import TLA.Def2




variable
  refm : System varsB → System varsA

record RefAction {α} {varsA : PSet α} {varsB : PSet α}
                 (refm : System varsB → System varsA) (actA : Action varsA) : Set (lsuc α) where
  field
    ract : Action varsB
    dom-embed : (vs : System varsB) → (cnd : cond ract vs) → cond actA (refm vs)
    range-embed : (vs : System varsB) → (nvs : System varsB)
                  → (cnd : cond ract vs) → (rsp : resp ract vs nvs)
                  → resp actA (refm vs) (refm nvs)
open RefAction public


⊥-RefAction : {refm : System varsB → System varsA} → RefAction {varsA = varsA} {varsB = varsB} refm actA
ract ⊥-RefAction = ⊥-Action
dom-embed ⊥-RefAction vs ()
range-embed ⊥-RefAction vs nvs () rsp



PRefAction : (B : Set α) → (refm : System {α} varsB → System {α} varsA) → (actA : Action varsA) → Set (lsuc α)
PRefAction {varsB = varsB} B refm actA = (b : B) → RefAction {varsB = varsB} refm actA


_toMPRefAction : {refm : System varsB → System varsA} → PRefAction {varsA = varsA} {varsB = varsB} B refm actA
                 → PRefAction {varsA = varsA} {varsB = varsB} (Maybe B) refm actA
(pref toMPRefAction) nothing = ⊥-RefAction
(pref toMPRefAction) (just b) = pref b



record RefPAction {α} {varsA : PSet α} {varsB : PSet α}
                 {B : Set α} (refm : System varsB → System varsA) (pactA : PAction B varsA) : Set (lsuc α) where
  field
    par : System varsB → B
    ract : Action varsB
    dom-embed : (vs : System varsB) → (cnd : cond ract vs) → cond (pactA (par vs)) (refm vs)
    range-embed : (vs : System varsB) → (nvs : System varsB)
                  → (cnd : cond ract vs) → (rsp : resp ract vs nvs)
                  → resp (pactA (par vs)) (refm vs) (refm nvs)
open RefPAction public


⊥-RefPAction : (par : System varsB → B) → {refm : System varsB → System varsA}
               → RefPAction {varsA = varsA} {varsB = varsB} {B = B} refm pactA
par (⊥-RefPAction par) = par
ract (⊥-RefPAction par) = ⊥-Action
dom-embed (⊥-RefPAction par) vs ()
range-embed (⊥-RefPAction par) vs nvs () rsp



PRefPAction : (E : Set α) → (refm : System {α} varsB → System {α} varsA) → (pactA : PAction B varsA)
             → Set (lsuc α)
PRefPAction {varsB = varsB} E refm pactA = (b : E) → RefPAction {varsB = varsB} refm pactA


-- Important here, We expect not to use the par function for an action that is not possible to happen.
_toMPRefPAction : {refm : System varsB → System varsA} → PRefPAction {varsA = varsA} {varsB = varsB} E refm pactA
                 → PRefPAction {varsA = varsA} {varsB = varsB} (Maybe E) refm pactA
(pref toMPRefPAction) nothing = ⊥-RefPAction IMPOSSIBLE
(pref toMPRefPAction) (just b) = pref b



record RefStAction {α} {varsA : PSet α} {varsB : PSet α}
                 (refm : System varsB → System varsA) : Set (lsuc α) where
  field
    ract : Action varsB
    isConst : (vs : System varsB) → (nvs : System varsB) → (cnd : cond ract vs)
              → (rsp : resp ract vs nvs)
              → refm vs ≡ refm nvs
open RefStAction public

⊥-RefStAction : {refm : System varsB → System varsA} → RefStAction {varsA = varsA} {varsB = varsB} refm
ract ⊥-RefStAction = ⊥-Action
isConst ⊥-RefStAction vs nvs () rsp


PRefStAction : (B : Set α) → (refm : System {α} varsB → System {α} varsA)
               → Set (lsuc α)
PRefStAction {varsA = varsA} {varsB = varsB} B refm = (b : B) → RefStAction {varsA = varsA} {varsB = varsB} refm


_toMPRefStAction : {refm : System varsB → System varsA} → PRefStAction {varsA = varsA} {varsB = varsB} B refm
                 → PRefStAction {varsA = varsA} {varsB = varsB} (Maybe B) refm
(refSt toMPRefStAction) nothing = ⊥-RefStAction
(refSt toMPRefStAction) (just b) = refSt b



RefSpec : (refm : System {α} varsB → System {α} varsA) → (spec : Spec varsA) → Set (lsuc α) 
RefSpec {varsA = varsA} {varsB = varsB} refm [] = List (RefStAction {varsA = varsA} {varsB = varsB} refm)
RefSpec {varsB = varsB} refm (act ∷ spec)
  = List (RefAction {varsB = varsB} refm act) × RefSpec {varsB = varsB} refm spec


variable
  refSp : RefSpec {varsA = _} {varsB = _} _ _


extractSpec : {refm : System varsB → System varsA} → RefSpec {varsA = varsA} {varsB = varsB} refm spec → Spec varsB
extractSpec {spec = []} rsp = map ract rsp
extractSpec {spec = act ∷ spec} (lra , rsp) =  (map ract lra) ++ extractSpec rsp




data GRefSpec {α varsA varsB} (refm : System {α} varsB → System {α} varsA)
              : ∀{PB} (PE : PESet α) (gspec : GSpec varsA PB) → Set (lsuc α) where
  rfA    : (ref : RefSpec {varsA = varsA} {varsB = varsB} refm spec)
           → GRefSpec refm ⊤ₑ (gsp spec psp∅)
  prfStA : (refSt : PRefStAction {varsA = varsA} {varsB = varsB} E refm)
           → (ind : GRefSpec {varsA = varsA} {varsB = varsB} refm PE (gsp spec psp∅))
           → GRefSpec refm (E ×ₑ PE) (gsp spec psp∅)
  prfA   : ∀{actA spec} → (prefA : PRefAction {varsA = varsA} {varsB = varsB} E refm actA)
           → let indf x = GRefSpec {varsA = varsA} {varsB = varsB} refm PE (gsp x psp∅)
             in (ind : indf (actA ∷ spec) ⊎ indf spec)
           → GRefSpec refm (E ×ₑ PE) (gsp (actA ∷ spec) psp∅)
  rfpA   : (refPA : RefPAction {varsA = varsA} {varsB = varsB} refm pact)
           → let indf y x = GRefSpec {varsB = varsB} refm {PB = y} PE (gsp spec x)
             in (ind : indf (B ×ₑ PB) (pact +psp+ pspec) ⊎ indf PB pspec)
           → GRefSpec refm PE (gsp spec (_+psp+_ {B = B} {PB = PB} pact pspec))
  prfpA  : (prefPA : PRefPAction {varsA = varsA} {varsB = varsB} E refm pact)
           → let indf y x = GRefSpec {varsB = varsB} refm {PB = y} PE (gsp spec x)
             in (ind : indf (B ×ₑ PB) (_+psp+_ pact pspec) ⊎ indf PB pspec)
           → GRefSpec refm {PB = (B ×ₑ PB)} (E ×ₑ PE) (gsp spec (_+psp+_ pact pspec))



_$ʳᶠ_ : {refm : System varsB → System varsA} → GRefSpec {varsB = varsB} refm PE gspec → (pe : pStoS (PE toMPESet)) → RefSpec {varsA = varsA} {varsB = varsB} refm (gspec $ᵍˢ pe)
rfA ref $ʳᶠ pe = ref
prfStA refSt gspec $ʳᶠ pe = {!!}
prfA prefA ind $ʳᶠ pe = {!!}
rfpA refPA ind $ʳᶠ pe = {!!}
prfpA prefPA ind $ʳᶠ pe = {!!}
