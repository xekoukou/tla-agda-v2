module TLA.RefineTheorem where

open import TLA.Refine2



record RefActionApp {α n k} {varsA : VSet {α} n} {varsB : VSet {α} k}
                 (refm : System varsB → System varsA) (actA : Action varsA) (sys : System varsB) : Set (lsuc α) where
  field
    ract : Action varsB
    dom-embed : (cnd : cond ract sys) → cond actA (refm sys)
    range-embed : (nsys : System varsB)
                  → (cnd : cond ract sys) → (rsp : resp ract sys nsys)
                  → resp actA (refm sys) (refm nsys)
open RefActionApp public



rf_apply_ : {refm : System varsB → System varsA}
             → RefAction {varsA = varsA} {varsB = varsB} refm actA
             → (sys : System varsB)
             → RefActionApp {varsA = varsA} {varsB = varsB} refm actA sys
ract (rf ref apply sys) = ract ref
dom-embed (rf ref apply sys) = (dom-embed ref) sys 
range-embed (rf ref apply sys) = range-embed ref sys



⊥-RefActionApp : {refm : System varsB → System varsA} → {sys : System varsB}
                 → RefActionApp {varsA = varsA} {varsB = varsB} refm actA sys
ract ⊥-RefActionApp = ⊥-Action
dom-embed ⊥-RefActionApp ()
range-embed ⊥-RefActionApp nvs () rsp


PRefActionApp : (B : Set α) → (refm : System {α} varsB → System {α} varsA) → (actA : Action varsA)
             → (sys : System varsB) → Set (lsuc α)
PRefActionApp {varsB = varsB} B refm actA sys = (b : B) → RefActionApp {varsB = varsB} refm actA sys


prf_apply_ : {refm : System varsB → System varsA} → PRefAction {varsA = varsA} {varsB = varsB} B refm actA
                 → (sys : System varsB) → PRefActionApp {varsA = varsA} {varsB = varsB} B refm actA sys
(prf pref apply sys) b = rf (pref b) apply sys



_toMPRApp : {refm : System varsB → System varsA} → {sys : System varsB}
                    →  PRefActionApp {varsA = varsA} {varsB = varsB} B refm actA sys
                    →  PRefActionApp {varsA = varsA} {varsB = varsB} (Maybe B) refm actA sys
(pref toMPRApp) nothing = ⊥-RefActionApp
(pref toMPRApp) (just b) = pref b


-- Remove if unnecessary.
⊥-RefPAction : (par : System varsB → B) → {refm : System varsB → System varsA}
               → RefPAction {varsA = varsA} {varsB = varsB} {B = B} refm pactA
par (⊥-RefPAction par) = par
ract (⊥-RefPAction par) = ⊥-Action
dom-embed (⊥-RefPAction par) vs ()
range-embed (⊥-RefPAction par) vs nvs () rsp


rfp_apply_ : {refm : System varsB → System varsA}
             → (ref : RefPAction {varsA = varsA} {varsB = varsB} refm pactA)
             → (sys : System varsB)
             → RefActionApp {varsA = varsA} {varsB = varsB} refm (pactA (par ref sys)) sys
ract (rfp ref apply sys) = ract ref
dom-embed (rfp ref apply sys) = dom-embed ref sys
range-embed (rfp ref apply sys) = range-embed ref sys




prfp_apply_ : {refm : System varsB → System varsA}
                     → (ref : PRefPAction {varsA = varsA} {varsB = varsB} E refm pactA)
                     → (sys : System varsB) → (e : E)
                     → RefActionApp {varsA = varsA} {varsB = varsB} refm (pactA (par (ref e) sys)) sys
(prfp pref apply sys) e = rfp (pref e) apply sys


_toMPRPApp : {refm : System varsB → System varsA}
             → {ref : PRefPAction {varsA = varsA} {varsB = varsB} E refm pactA}
             → {sys : System varsB}
             → (refa : (e : E) → RefActionApp {varsA = varsA} {varsB = varsB} refm (pactA (par (ref e) sys)) sys)
             → (e : Maybe E)
             → RefActionApp {varsA = varsA} {varsB = varsB} refm (((λ e → pactA (par (ref e) sys)) toMPAction) e) sys
(ref toMPRPApp) nothing =  ⊥-RefActionApp
(ref toMPRPApp) (just e) = ref e



record RefStActionApp {α n k} {varsA : VSet {α} n} {varsB : VSet {α} k}
                 (refm : System varsB → System varsA) (sys : System varsB) : Set (lsuc α) where
  field
    ract : Action varsB
    isConst : (nsys : System varsB) → (cnd : cond ract sys)
              → (rsp : resp ract sys nsys)
              → refm sys ≡ refm nsys
open RefStActionApp public


rfSt_apply : {refm : System varsB → System varsA} → (ref : RefStAction {varsA = varsA} {varsB = varsB} refm)
             → (sys : System varsB)
             → RefStActionApp {varsA = varsA} {varsB = varsB} refm sys
ract (rfSt ref apply sys) = ract ref
isConst (rfSt ref apply sys) = isConst ref sys

PRefStActionApp : (E : Set α) → (refm : System {α} varsB → System {α} varsA)
                  → (sys : System varsB) → Set (lsuc α)
PRefStActionApp {varsA = varsA} {varsB = varsB} E refm sys
  = (e : E) → RefStActionApp {varsA = varsA} {varsB = varsB} refm sys

prfSt_apply : {refm : System varsB → System varsA} → (ref : PRefStAction {varsA = varsA} {varsB = varsB} E refm)
              → (sys : System varsB)
              → PRefStActionApp {varsA = varsA} {varsB = varsB} E refm sys
ract (prfSt ref apply sys e) = ract (ref e)
isConst (prfSt ref apply sys e) = isConst (ref e) sys


⊥-RefStActionApp : {refm : System varsB → System varsA} → {sys : System varsB}
                   → RefStActionApp {varsA = varsA} {varsB = varsB} refm sys
ract ⊥-RefStActionApp = ⊥-Action
isConst ⊥-RefStActionApp nsys () rsp


_toMPRStApp : {refm : System varsB → System varsA} → {sys : System varsB}
              → PRefStActionApp {varsA = varsA} {varsB = varsB} B refm sys
                 → PRefStActionApp {varsA = varsA} {varsB = varsB} (Maybe B) refm sys
(refSt toMPRStApp) nothing = ⊥-RefStActionApp
(refSt toMPRStApp) (just b) = refSt b


RefSpecApp : (refm : System {α} varsB → System {α} varsA) → (spec : Spec varsA)
             → (sys : System varsB) → Set (lsuc α) 
RefSpecApp {varsA = varsA} {varsB = varsB} refm [] sys
  = List (RefStActionApp {varsA = varsA} {varsB = varsB} refm sys)
RefSpecApp {varsB = varsB} refm (act ∷ spec) sys
  = List (RefActionApp {varsB = varsB} refm act sys) × RefSpecApp {varsB = varsB} refm spec sys


_addStApp_ : {refm : System {α} varsB → System {α} varsA} → {spec : Spec varsA} → {sys : System varsB}
        → RefSpecApp {varsB = varsB} refm spec sys → RefStActionApp {varsA = varsA} {varsB = varsB} refm sys
        → RefSpecApp {varsB = varsB} refm spec sys
_addStApp_ {spec = []} ref rfa = rfa ∷ ref
_addStApp_ {spec = act ∷ spec} (rfas , ind) rfa = rfas , (ind addStApp rfa)


-- Completely wrong. We need to apply PB not PE.
-- One needs to check that all refine records are turned into RefActionsApp
-- Otherwise the extension of the refTheorem to GrefSpec will not hold.
_$ʳᶠ_ : {refm : System varsB → System varsA} → GRefSpec {varsB = varsB} refm PE gspec
        → (pe : pStoS (PE toMPSet)) → (sys : System varsB)
        → RefSpecApp {varsA = varsA} {varsB = varsB} refm (gspec $ᵍˢ pe) sys
_$ʳᶠ_ {gspec = gsp [] _} (rf []) pe sys = []
_$ʳᶠ_ {gspec = gsp [] _} (rf (refSt ∷ ref)) pe sys = rfSt refSt apply sys ∷ (rf ref $ʳᶠ pe) sys
_$ʳᶠ_ {gspec = gsp (act ∷ sp) _} (rf ([] , ind)) pe sys = [] , (rf ind $ʳᶠ pe) sys
_$ʳᶠ_ {gspec = gsp (act ∷ sp) _} (rf (ract ∷ refA , ind)) pe sys
  = let (rfs , rfsts) = (rf (refA , ind) $ʳᶠ pe) sys
    in ((rf ract apply sys) ∷ rfs) , rfsts
_$ʳᶠ_ {gspec = gsp [] _} (pst refSt ∷ gref) (e , pe) sys
  = let w = (gref $ʳᶠ pe) sys
    in ((prfSt refSt apply sys) toMPRStApp) e ∷ w
_$ʳᶠ_ {gspec = gsp (act ∷ sp) _} (pst refSt ∷ gref) (e , pe) sys
  = let (rfas , rsp) = (gref $ʳᶠ pe) sys
    in (rfas , rsp addStApp ((prfSt refSt apply sys) toMPRStApp) e )
((prf prefA ∷ left ind) $ʳᶠ (e , pe)) sys
  = let (l , rm) = (ind $ʳᶠ pe) sys
    in (((prf prefA apply sys) toMPRApp) e ∷ l) , rm
((prf prefA ∷ right ind) $ʳᶠ (e , pe)) sys
  = let rm = (ind $ʳᶠ pe) sys
    in (((prf prefA apply sys) toMPRApp) e ∷ []) , rm
((rfp refPA ∷ left ind) $ʳᶠ pe) sys
  = let (l , rm) = (ind $ʳᶠ pe) sys
    in {!!}
((rfp refPA ∷ right ind) $ʳᶠ pe) sys = {!!}
((prfp prefPA ∷ ind) $ʳᶠ pe) sys = {!!}
