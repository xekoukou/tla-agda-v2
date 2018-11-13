module TLA.Refine where

open import TLA.Def
open import LTL.Product

open import Prelude.List hiding ([_])
open import Prelude.Function

data _∈ₗ_ {α} {A : Set α} (a : A) : List A → Set α where
  instance
    zero : ∀ {x xs} → a ∈ₗ (x ∷ xs)
    suc : ∀ {x xs} (i : a ∈ₗ xs) → a ∈ₗ (x ∷ xs)






variable
  refm refmA refmB : System _ → System _

record RefAction {α n k} {varsA : Vec (Set α) (suc n)} {varsB : Vec (Set α) (suc k)}
                 (refm : System varsB → System varsA) (actA : Action varsA) : Set (lsuc α) where
  field
    ract : Action varsB
    dom-embed : (vs : System varsB) → (cnd : cond ract vs) → cond actA (refm vs)
    range-embed : (vs : System varsB) → (nvs : System varsB)
                  → (cnd : cond ract vs) → (rsp : resp ract vs nvs)
                  → resp actA (refm vs) (refm nvs)
open RefAction public


PRefAction : (B : Set α) → (refm : System {α} varsB → System {α} varsA) → (actA : Action varsA) → Set (lsuc α)
PRefAction {varsB = varsB} B refm actA = (b : B) → RefAction {varsB = varsB} refm actA

-- 
-- prefToRefA : {refm : System varsB → System varsA} → PRefAction {varsB = varsB} B refm actA → RefAction {varsA = varsA} {varsB = varsB} refm actA
-- ract (prefToRefA prefa) = PAtoA (λ b → ract (prefa b))
-- dom-embed (prefToRefA prefa) sys (b , cnd) = dom-embed (prefa b) sys cnd
-- range-embed (prefToRefA prefa) sys nsys (b , cnd) = range-embed (prefa b) sys nsys cnd
-- 

record RefPAction {α n k} {varsA : Vec (Set α) (suc n)} {varsB : Vec (Set α) (suc k)}
                 {B : Set α} (refm : System varsB → System varsA) (pactA : PAction B varsA) : Set (lsuc α) where
  field
    par : System varsB → B
    ract : Action varsB
    dom-embed : (vs : System varsB) → (cnd : cond ract vs) → cond (pactA (par vs)) (refm vs)
    range-embed : (vs : System varsB) → (nvs : System varsB)
                  → (cnd : cond ract vs) → (rsp : resp ract vs nvs)
                  → resp (pactA (par vs)) (refm vs) (refm nvs)
open RefPAction public


-- 
-- refpToRefA : {refm : System varsB → System varsA} → RefPAction {varsB = varsB} refm pactA → RefAction {varsA = varsA} {varsB = varsB} refm (PAtoA pactA)
-- ract (refpToRefA refpa) = ract refpa
-- dom-embed (refpToRefA refpa) sys cnd = ((par refpa) sys ) , ((dom-embed refpa) sys cnd)
-- range-embed (refpToRefA refpa) = range-embed refpa
-- 
-- 

PRefPAction : (E : Set α) → (refm : System {α} varsB → System {α} varsA) → (pactA : PAction B varsA)
             → Set (lsuc α)
PRefPAction {varsB = varsB} E refm pactA = (b : E) → RefPAction {varsB = varsB} refm pactA

-- 
-- prefpToRefA : {refm : System varsB → System varsA} → PRefPAction {varsB = varsB} E refm pactA → RefAction {varsA = varsA} {varsB = varsB} refm (PAtoA pactA)
-- ract (prefpToRefA ref) = PAtoA (λ e → ract (ref e))
-- dom-embed (prefpToRefA ref) vs (e , cnd) = par (ref e) vs , dom-embed (ref e) vs cnd
-- range-embed (prefpToRefA ref) vs nvs (e , cnd) rsp = range-embed (ref e) vs nvs cnd rsp
-- 
-- 

record RefStAction {α n k} {varsA : Vec (Set α) (suc n)} {varsB : Vec (Set α) (suc k)}
                 (refm : System varsB → System varsA) : Set (lsuc α) where
  field
    ract : Action varsB
    isConst : (vs : System varsB) → (nvs : System varsB) → (cnd : cond ract vs)
              → (rsp : resp ract vs nvs)
              → refm vs ≡ refm nvs
open RefStAction public



PRefStAction : (B : Set α) → (refm : System {α} varsB → System {α} varsA)
               → Set (lsuc α)
PRefStAction {varsA = varsA} {varsB = varsB} B refm = (b : B) → RefStAction {varsA = varsA} {varsB = varsB} refm

-- 
-- prefSttoA : {refm : System varsB → System varsA} → PRefStAction {varsA = varsA} {varsB = varsB} B refm → RefStAction {varsA = varsA} {varsB = varsB} refm
-- ract (prefSttoA ref) = PAtoA (λ b → ract (ref b))
-- isConst (prefSttoA ref) vs nvs (b , cnd) rsp = isConst (ref b) vs nvs cnd rsp
-- 

RefSpec : (refm : System {α} varsB → System {α} varsA) → (spec : Spec varsA) → Set (lsuc α) 
RefSpec {varsA = varsA} {varsB = varsB} refm [] = List (RefStAction {varsA = varsA} {varsB = varsB} refm)
RefSpec {varsB = varsB} refm (act ∷ spec)
  = List (RefAction {varsB = varsB} refm act) × RefSpec {varsB = varsB} refm spec


variable
  refSp : RefSpec {varsA = _} {varsB = _} _ _



exSp : {refm : System varsB → System varsA} → RefSpec {varsA = varsA} {varsB = varsB} refm spec → Spec varsB
exSp {spec = []} rsp = map ract rsp
exSp {spec = act ∷ spec} (lra , rsp) =  (map ract lra) ++ exSp rsp



data GRefSpec {α n k varsA varsB} (refm : System {α} {n} varsB → System {α} {k} varsA)
              : ∀{PB} (PE : PSet α) (pspec : GSpec varsA PB) → Set (lsuc α) where
  rfA    : (ref : RefSpec {varsA = varsA} {varsB = varsB} refm spec)
           → GRefSpec refm ⊤ₚ (gsp spec s∅)
  prfStA : (refSt : PRefStAction {varsA = varsA} {varsB = varsB} E refm)
           → (ind : GRefSpec {varsA = varsA} {varsB = varsB} refm PE (gsp spec s∅)) → GRefSpec refm (E ×ₚ PE) (gsp spec s∅)
  prfA   : ∀{actA spec} → (prefA : PRefAction {varsA = varsA} {varsB = varsB} E refm actA) → let indf x = GRefSpec {varsA = varsA} {varsB = varsB} refm PE (gsp x s∅) in (ind : indf (actA ∷ spec) ⊎ indf spec)
           → GRefSpec refm (E ×ₚ PE) (gsp (actA ∷ spec) s∅)
  rfpA : (refPA : RefPAction {varsA = varsA} {varsB = varsB} refm pact)
         → let indf y x = GRefSpec {varsB = varsB} refm {PB = y} PE (gsp spec x) in (ind : indf (B ×ₚ PB) (spPA pact pspec) ⊎ indf PB pspec)
         → GRefSpec refm PE (gsp spec (spPA {B = B} {PB = PB} pact pspec))
  prfpA : (prefPA : PRefPAction {varsA = varsA} {varsB = varsB} E refm pact)
          → let indf y x = GRefSpec {varsB = varsB} refm {PB = y} PE (gsp spec x) in (ind : indf (B ×ₚ PB) (spPA pact pspec) ⊎ indf PB pspec) → GRefSpec refm {PB = (B ×ₚ PB)} (E ×ₚ PE) (gsp spec (spPA pact pspec))





trefm : (refm : System varsB → System varsA) → (System varsB)ʷ → (System varsA)ʷ
trefm refm beh = ⟨ refm ⟩ $ʷ beh

-- 
-- gdecF : {refm : System varsB → System varsA} → {spec : Spec varsA} → {beh : (System varsB)ʷ}
--        → {refSp : RefSpec {varsB = varsB} refm spec} → (decFp : [ ⟨ DecF (exSp refSp) ⟩ $ʷ beh ])
--        → [ ⟨ DecF spec ⟩ $ʷ (⟨ refm ⟩ $ʷ beh) ] → [ TRestr (exSp refSp) beh decFp ⇒ ⟨ DecF spec ⟩ $ʷ (⟨ refm ⟩ $ʷ beh) ]
-- gdecF {refm = refm} {[]} {beh} {refSp} decFp adecF rst n = unit
-- gdecF {refm = refm} {act ∷ spec} {beh} {[] , refSp} decFp adecF n rst
--   = fst (adecF n) , gdecF {spec = spec} {refSp = refSp} decFp (λ sys → snd (adecF sys)) n rst
-- gdecF {refm = refm} {act ∷ spec} {beh} {ract ∷ lact , refSp} decFp adecF n rst with fst (decFp n) 
-- gdecF {refm = refm} {act ∷ spec} {beh} {ract ∷ lact , refSp} decFp adecF n rst | fst = {!!}
-- 
-- 
-- refTheorem : (refm : System varsB → System varsA) → (spec : Spec varsA) → (beh : (System varsB)ʷ)
--              → (refSp : RefSpec {varsB = varsB} refm spec) → (decFp : [ ⟨ DecF (exSp refSp) ⟩ $ʷ beh ])
--              → (decF : [ ⟨ DecF spec ⟩ $ʷ (⟨ refm ⟩ $ʷ beh) ])
--              → (rst : [ TRestr (exSp refSp) beh decFp ]) → [ TRestr spec ( ⟨ refm ⟩ $ʷ beh) (gdecF decFp decF $ʷ rst) ]
-- refTheorem = {!!}
-- 


refStLemma : (refm : System varsB → System varsA) → (beh : (System varsB)ʷ) → (refSp : RefSpec {varsA = varsA} {varsB = varsB} refm []) → (decFp : DecF (exSp refSp)) 
             → [ TRestr (exSp refSp) beh decFp ⇒ ⟨ _≡_ ⟩ $ʷ (⟨ refm ⟩ $ʷ beh) $ʷ (⟨ refm ⟩ $ʷ (○ beh)) ]
refStLemma refm beh [] decFp n (left rst) = ⊥′-elim rst
refStLemma refm beh (ract ∷ refSp) decFp n (left rst) with decFp (beh n) | refStLemma refm beh refSp (λ sys → snd (decFp sys)) n
refStLemma refm beh (ract ∷ refSp) decFp n (left (left rst)) | yes d , snd | g = isConst ract (beh n) (beh (suc n)) d rst 
refStLemma refm beh (ract ∷ refSp) decFp n (left (right rst)) | yes d , snd | g = g (left rst)
refStLemma refm beh (ract ∷ refSp) decFp n (left rst) | no d , snd | g = g (left rst)
refStLemma refm beh refSp decFp n (right rst) = cong refm rst



--- Theorem
--- A behavior beh induces a behavior ⟨ refm ⟩ $ʷ beh through the refinement mapping that respects the restrictions of the more abstract model.

refTheorem : (refm : System varsB → System varsA) → (spec : Spec varsA) → (beh : (System varsB)ʷ) → (refSp : RefSpec {varsB = varsB} refm spec) → (decFp : DecF (exSp refSp)) → (decF : DecF spec)
             → [ TRestr (exSp refSp) beh decFp ⇒ TRestr spec ( ⟨ refm ⟩ $ʷ beh ) decF ]
refTheorem refm [] beh refSp decFp decF n rst = right (refStLemma refm beh refSp decFp n rst)
refTheorem refm (act ∷ spec) beh ([] , refSp) decFp decF n rst with decF (refm (beh n)) | refTheorem refm spec beh refSp decFp (λ sys → snd (decF sys)) n rst
refTheorem refm (act ∷ spec) beh ([] , refSp) decFp decF n rst | yes d , snd | left ind = left (right ind)
refTheorem refm (act ∷ spec) beh ([] , refSp) decFp decF n rst | yes d , snd | right ind = right ind
refTheorem refm (act ∷ spec) beh ([] , refSp) decFp decF n rst | no d , snd | g = g
refTheorem refm (act ∷ spec) beh (ract ∷ rs , refSp) decFp decF n (right rst) = right (cong refm rst)
refTheorem refm (act ∷ spec) beh (ract ∷ rs , refSp) decFp decF n (left rst) with decFp (beh n) | refTheorem refm (act ∷ spec) beh (rs , refSp) (λ sys → snd (decFp sys)) decF n
refTheorem refm (act ∷ spec) beh (ract ∷ rs , refSp) decFp decF n (left rst) | yes dra , sndra | g with decF (refm (beh n))
refTheorem refm (act ∷ spec) beh (ract ∷ rs , refSp) decFp decF n (left (left rst)) | yes dra , sndra | g | yes da , snda = left (left {!range-embed ract (beh n) ? ? ?!}) -- left (left (range-embed ract (beh n) (beh (suc n)) dra da rst))
refTheorem refm (act ∷ spec) beh (ract ∷ rs , refSp) decFp decF n (left (right rst)) | yes dra , sndra | g | yes da , snda = g (left rst)
refTheorem refm (act ∷ spec) beh (ract ∷ rs , refSp) decFp decF n (left rst) | yes dra , sndra | g | no da , snda =  ⊥-elim (da (dom-embed ract (beh n) dra))
refTheorem refm (act ∷ spec) beh (ract ∷ rs , refSp) decFp decF n (left rst) | no dra , sndra | g = g (left rst)



-- -- Terminating is used here for the rfpA case.
-- {-# TERMINATING #-}
-- exPSp : {refm : System varsB → System varsA} → (gref : GRefSpec {varsA = varsA} {varsB = varsB} refm PE gspec)
--         → GSpec varsB PE
-- exPSp (rfA ref) = gsp (exSp ref) s∅
-- exPSp (prfStA refSt gref) =
--   let cind = exPSp gref
--   in gsp (gToSpec cind) (spPA (λ e → ract (refSt e)) (gToPSpec cind))
-- exPSp (prfA prefA ind) =
--   let cind = either exPSp exPSp ind
--   in gsp (gToSpec cind) (spPA (λ e → ract (prefA e)) (gToPSpec cind))
-- exPSp (rfpA refPA ind) =
--   let cind = either exPSp exPSp ind
--   in gsp (ract refPA ∷ gToSpec cind) (gToPSpec cind)
-- exPSp (prfpA prefPA ind) =
--   let cind = either exPSp exPSp ind
--   in gsp (gToSpec cind) (spPA (λ e → ract (prefPA e)) (gToPSpec cind))
  


-- --- I just need to reduce this to the case where there are no parameters. We do it by picking some of the parameters of PE and then based on them,
-- -- pick PB parameters. Then We reduce the parametrized refinement records to simple refinement records and use the initial theorem.


-- -- conDecF : (refm : System varsB → System varsA) → (gspec : GSpec varsA PB)
-- --        → (gref : GRefSpec {varsB = varsB} refm PE gspec) → (gdecFp : GDecF PE (exPSp gref)) → GDecF PE gspec
-- -- conDecF {PB = PB} {PE = PE} refm gspec gref gdecFp = {!!}



-- -- -- refPTheorem : (refm : System varsB → System varsA) → (gspec : GSpec varsA PB) → (beh : (System varsB)ʷ)
-- -- --               → (gref : GRefSpec {varsB = varsB} refm PE gspec) → (gdecFp : GDecF PE (exPSp gref)) → (gdecF : GDecF PB gspec)
-- -- --               → [ GTRestr PE (exPSp gref) beh gdecFp ⇒ GTRestr PB gspec ( ⟨ refm ⟩ $ʷ beh ) gdecF ]

-- -- -- -- Proving it for the simple case where we do not have parametrized Actions. Using the above theorem.
-- -- -- refPTheorem refm (gsp spec s∅) beh (rfA ref) gdecFp gdecF n (left rst) = left (refTheorem refm spec beh ref (fst gdecFp) (fst gdecF) n rst)

-- -- -- -- This is unnecessary complexity. (but probably unavoidable).
-- -- -- refPTheorem refm .(gsp _ s∅) beh (rfA ref) gdecFp gdecF n (right (_ , left empty)) = ⊥′-elim empty
-- -- -- refPTheorem refm .(gsp _ s∅) beh (rfA ref) gdecFp gdecF n (right (_ , right eq)) = right (unit , right (cong refm eq))

-- -- -- -- With is needed here to turm exPSp gref into (gsp _ _) for the reduction of GDecF function, the type of gdecFp
-- -- -- refPTheorem refm (gsp spec s∅) beh (prfStA refSt gref) gdecFp gdecF n (left rst) with exPSp gref | refPTheorem refm (gsp spec s∅) beh gref
-- -- -- refPTheorem refm (gsp spec s∅) beh (prfStA refSt gref) (decFp , _ , pdecFp) gdecF n (left rst) | gsp _ _ | g = g (decFp , pdecFp) gdecF n (left rst)


-- -- -- refPTheorem refm gspec@(gsp _ s∅) beh (prfStA refSt gref) (decFp , ldecFp , pdecFp) gdecF n (right ((e , pe) , left rst)) with ldecFp e (beh n)
-- -- -- refPTheorem refm (gsp spec s∅) beh (prfStA refSt gref) (decFp , ldecFp , pdecFp) gdecF n (right ((e , pe) , left (left resp))) | yes cnd = left (right (isConst (refSt e) (beh n) (beh (suc n)) cnd resp))

-- -- -- -- We use 'with exPSp' to change the type of g with regards to (decFp , pdecFp) GDecF _ ?
-- -- -- -- In the first case, beh could perform the retSt action because the condition is met, but another action is "chosen" instead.
-- -- -- -- In the second case, the condition is not met and thus the action cannot be performed.
-- -- -- -- In both cases, the proof is the same.
-- -- -- refPTheorem refm gspec@(gsp _ s∅) beh (prfStA refSt gref) (decFp , ldecFp , pdecFp) gdecF n (right ((e , pe) , left (right rst))) | yes cnd with exPSp gref | refPTheorem refm gspec beh gref
-- -- -- refPTheorem refm (gsp _ s∅) beh (prfStA refSt gref) (decFp , _ , pdecFp) gdecF n (right ((e , pe) , left (right rst))) | yes cnd | gsp _ _ | g = g (decFp , pdecFp) gdecF n (right (pe , left rst))

-- -- -- refPTheorem refm gspec@(gsp _ s∅) beh (prfStA refSt gref) (decFp , ldecFp , pdecFp) gdecF n (right ((e , pe) , left rst)) | no cnd with exPSp gref | refPTheorem refm gspec beh gref
-- -- -- refPTheorem refm (gsp _ s∅) beh (prfStA refSt gref) (decFp , ldecFp , pdecFp) gdecF n (right ((e , pe) , left rst)) | no cnd | gsp _ _ | g = g (decFp , pdecFp ) gdecF n (right (pe , left rst))


-- -- -- refPTheorem refm .(gsp _ s∅) beh (prfStA refSt gref) gdecFp gdecF n (right ((e , pe) , right eq)) = left (right (cong refm eq))

-- -- -- -- With is needed here to turm exPSp gref into (gsp _ _) for the reduction of GDecF function, the type of gdecFp
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (left gref)) gdecFp gdecF n (left rst) with exPSp gref | refPTheorem refm (gsp (actA ∷ spec) s∅) beh gref
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (left gref)) (decFp , _ , pdecFp) gdecF n (left rst) | gsp _ _ | g = g (decFp , pdecFp) gdecF n (left rst)

-- -- -- -- All withs in this case are used to reduce the types. This is the same proof as in the previous step.
-- -- -- -- Since we have (left rst) , we can prove that beh obeys all the restrictions of the other actions, ignoring actA.
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (right gref)) (decFp , _ , pdecFp) (decF , _ ) n (left rst) with exPSp gref | refPTheorem refm (gsp spec s∅) beh gref 
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (right gref)) (decFp , _ , pdecFp) (decF , _ ) n (left rst) | gsp _ _ | g with decF (refm (beh n)) | g (decFp , pdecFp) ((λ sys → snd (decF sys)) , unit) n (left rst)
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (right gref)) (decFp , _ , pdecFp) (decF , _ ) n (left rst) | gsp _ _ | g | yes da , snda | left (left gg) = left (left (right gg))
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (right gref)) (decFp , _ , pdecFp) (decF , _ ) n (left rst) | gsp _ _ | g | yes da , snda | left (right eq) = left (right eq) 
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (right gref)) (decFp , _ , pdecFp) (decF , _ ) n (left rst) | gsp _ _ | g | yes da , snda | right (_ , left empty) = ⊥′-elim empty
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (right gref)) (decFp , _ , pdecFp) (decF , _ ) n (left rst) | gsp _ _ | g | yes da , snda | right (_ , right eq) = left (right eq)
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (right gref)) (decFp , _ , pdecFp) (decF , _ ) n (left rst) | gsp _ _ | g | no da , snda | gg = gg

-- -- -- -- same as before expect that now , we do have the possibility of prefA happening because rst is PTRestr.
-- -- -- -- since pspec is s∅, as before we need to show that TRestr holds.
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (left gref)) gdecFp (decF , _) n (right ((e , pe) , rst)) with exPSp gref | refPTheorem refm (gsp (actA ∷ spec) s∅) beh gref
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (left gref)) (decFp , ldecFp , pdecFp) (decF , _) n (right ((e , pe) , left rst)) | gsp _ _ | g with decF (refm (beh n)) | ldecFp e (beh n) | g (decFp , pdecFp) (decF , unit) n
-- -- -- -- the paction is selected from rst.
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (left gref)) (decFp , ldecFp , pdecFp) (decF , _) n (right ((e , pe) , left (left rst))) | gsp _ _ | g | yes da , snda | yes dfa | gg = left (left (left (range-embed (prefA e) (beh n) (beh (suc n)) dfa da rst)))
-- -- -- -- the paction is not selected from rst.
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (left gref)) (decFp , ldecFp , pdecFp) (decF , _) n (right ((e , pe) , left (right rst))) | gsp _ _ | g | yes da , snda | yes dfa | gg = gg (right (pe , left rst))
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (left gref)) (decFp , ldecFp , pdecFp) (decF , _) n (right ((e , pe) , left rst)) | gsp _ _ | g | no da , snda | yes dfa | gg = ⊥-elim (da (dom-embed (prefA e) (beh n) dfa))
-- -- -- -- rst cannot select it because the cnd is not met.
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (left gref)) (decFp , ldecFp , pdecFp) (decF , _) n (right ((e , pe) , left rst)) | gsp _ _ | g | da , snda | no dfa | gg = gg (right (pe , left rst))

-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (left gref)) (decFp , _ , pdecFp) (decF , _) n (right ((e , pe) , right eq)) | gsp _ _ | g = left (right (cong refm eq))

-- -- -- -- same as before , but the next step does not have actA, so minor changes.
-- -- -- ----------------------------------------
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (right gref)) gdecFp (decF , _) n (right ((e , pe) , rst)) with exPSp gref | refPTheorem refm (gsp spec s∅) beh gref
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (right gref)) (decFp , ldecFp , pdecFp) (decF , _) n (right ((e , pe) , left rst)) | gsp _ _ | g  with decF (refm (beh n)) | ldecFp e (beh n) | g (decFp , pdecFp) ((λ sys → snd (decF sys)) , unit) n
-- -- -- -- the paction is selected from rst.
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (right gref)) (decFp , ldecFp , pdecFp) (decF , _) n (right ((e , pe) , left (left rst))) | gsp _ _ | g | yes da , snda | yes dfa | gg = left (left (left (range-embed (prefA e) (beh n) (beh (suc n)) dfa da rst)))
-- -- -- -- the paction is not selected from rst.
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (right gref)) (decFp , ldecFp , pdecFp) (decF , _) n (right ((e , pe) , left (right rst))) | gsp _ _ | g | yes da , snda | yes dfa | gg
-- -- --   = case gg (right (pe , left rst)) of λ { (left (left x)) → left (left (right x)) ; (left (right x)) → left (right x) ; (right x) → right x}
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (right gref)) (decFp , ldecFp , pdecFp) (decF , _) n (right ((e , pe) , left rst)) | gsp _ _ | g | no da , snda | yes dfa | gg = ⊥-elim (da (dom-embed (prefA e) (beh n) dfa))
-- -- -- -- rst cannot select it because the cnd is not met.
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (right gref)) (decFp , ldecFp , pdecFp) (decF , _) n (right ((e , pe) , left rst)) | gsp _ _ | g | yes x , snda | no dfa | gg
-- -- --   = case gg (right (pe , left rst)) of λ { (left (left x)) → left (left (right x))
-- -- --                                          ; (left (right x)) → left (right x)
-- -- --                                          ; (right x) → right x}
-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (right gref)) (decFp , ldecFp , pdecFp) (decF , _) n (right ((e , pe) , left rst)) | gsp _ _ | g | no x , snda | no dfa | gg = gg (right (pe , left rst))

-- -- -- refPTheorem refm (gsp (actA ∷ spec) s∅) beh (prfA prefA (right gref)) (decFp , _ , pdecFp) (decF , _) n (right ((e , pe) , right eq)) | gsp _ _ | g = left (right (cong refm eq))


-- -- -- refPTheorem refm (gsp spec (spPA pact pref)) beh (rfpA refPA (left gref)) (decFp , epdecFp) (decF , bpdecF) n (left rst) with exPSp gref | refPTheorem refm (gsp spec (spPA pact pref)) beh gref
-- -- -- refPTheorem refm (gsp spec (spPA pact pref)) beh (rfpA refPA (left gref)) (decFp , epdecFp) (decF , bpdecF) n (left rst) | gsp _ _ | g with decFp (beh n) | g ((λ sys → snd (decFp sys)) , epdecFp)
-- -- -- -- rst selects the action
-- -- -- refPTheorem refm (gsp spec (spPA pact pref)) beh (rfpA refPA (left gref)) (decFp , epdecFp) (decF , ldecF , pdecF) n (left (left (left rst))) | gsp _ _ | g | yes da , snda | gg = {!!} -- right (((par refPA) (beh n) , {!!}) , {!!})
-- -- -- -- rst selects the inductive step
-- -- -- refPTheorem refm (gsp spec (spPA pact pref)) beh (rfpA refPA (left gref)) (decFp , epdecFp) (decF , bpdecF) n (left (left (right rst))) | gsp _ _ | g | yes da , snda | gg = {!!}
-- -- -- refPTheorem refm (gsp spec (spPA pact pref)) beh (rfpA refPA (left gref)) (decFp , epdecFp) (decF , bpdecF) n (left (right rst)) | gsp _ _ | g | yes da , snda | gg = left (right (cong refm rst))
-- -- -- -- The absence of the condition limits the proof to the inductive step.
-- -- -- refPTheorem refm (gsp spec (spPA pact pref)) beh (rfpA refPA (left gref)) (decFp , epdecFp) (decF , bpdecF) n (left (left rst)) | gsp _ _ | g | no da , snda | gg = {!!}
-- -- -- refPTheorem refm (gsp spec (spPA pact pref)) beh (rfpA refPA (left gref)) (decFp , epdecFp) (decF , bpdecF) n (left (right rst)) | gsp _ _ | g | no da , snda | gg = left (right (cong refm rst))
-- -- -- refPTheorem refm (gsp spec (spPA pact pref)) beh (rfpA refPA (left gref)) gdecFp (decF , ldecF , pdecF) n (right rst) = {!!}


-- -- -- refPTheorem refm (gsp spec (spPA pact pref)) beh (rfpA refPA (right gref)) gdecFp gdecF n (left rst) = {!!}
-- -- -- refPTheorem refm (gsp spec (spPA pact pref)) beh (rfpA refPA (right gref)) gdecFp gdecF n (right rst) = {!!}

-- -- -- refPTheorem refm (gsp spec (spPA pact pref)) beh (prfpA prefPA ind) gdecFp gdecF n rst = {!!}



-- -- -- -- refPLemma2 : (refm : System varsB → System varsA) → (beh : (System varsB)ʷ)
-- -- -- --               → (prefSp : GRefSpec {varsA = varsA} {varsB = varsB} refm PE s∅) → (pdecFp : PDecF PE (exPSp prefSp))
-- -- -- --               → [ PTRestr PE (exPSp prefSp) beh pdecFp ⇒ PTRestr {vars = varsA} ⊤ₚ s∅ ( ⟨ refm ⟩ $ʷ beh ) (λ b sys → unit) ]
-- -- -- -- refPLemma2 refm beh (rfStA rfSt prefSp) pdecFp n rst = {!!}
-- -- -- -- refPLemma2 refm beh (rfPStA rfSt prefSp) pdecFp n rst = {!!}
-- -- -- -- refPLemma2 refm beh rf∅ pdecFp n (_ , left rst) = ⊥′-elim rst
-- -- -- -- refPLemma2 refm beh rf∅ pdecFp n (_ , right rst) = unit , right (cong refm rst)

-- -- -- -- refPTheorem2 : (refm : System varsB → System varsA) → (pspec : PSpec varsA PB) → (beh : (System varsB)ʷ)
-- -- -- --               → (prefSp : GRefSpec {varsB = varsB} refm PE pspec) → (pdecFp : PDecF PE (exPSp prefSp)) → (pdecF : PDecF PB pspec)
-- -- -- --               → [ PTRestr PE (exPSp prefSp) beh pdecFp ⇒ PTRestr PB pspec ( ⟨ refm ⟩ $ʷ beh ) pdecF ]
-- -- -- -- refPTheorem2 refm (spA act pspec) beh prefSp pdecFp pdecF n rst = {!!}
-- -- -- -- refPTheorem2 refm (spPA pact pspec) beh prefSp pdecFp pdecF n rst = {!!}
-- -- -- -- refPTheorem2 {PE = PE} refm s∅ beh prefSp pdecFp pdecF = refPLemma2 refm beh prefSp pdecFp


-- -- -- -- refPTheorem : (refm : System varsB → System varsA) → (pspec : PSpec varsA PB) → (beh : (System varsB)ʷ)
-- -- -- --               → (prefSp : GRefSpec {varsB = varsB} refm PE pspec) → (pdecFp : PDecF PE (exPSp prefSp)) → (pdecF : PDecF PB pspec)
-- -- -- --               → [ PTRestr PE (exPSp prefSp) beh pdecFp ⇒ PTRestr PB pspec ( ⟨ refm ⟩ $ʷ beh ) pdecF ]
-- -- -- -- refPTheorem refm (spA act pspec) beh prefSp pdecFp pdecF n rst = {!!}
-- -- -- -- refPTheorem refm (spPA pact pspec) beh prefSp pdecFp pdecF n rst = {!!}
-- -- -- -- refPTheorem {PE = PE} refm s∅ beh (rfStA rfSt prefSp) pdecFp pdecF n rst = {!!}
-- -- -- -- refPTheorem {PE = E ×ₚ PE} refm s∅ beh (rfPStA rfSt prefSp) pdecFp pdecF n ((e , pe) , left rst) with pdecFp (e , pe) (beh n) | refPTheorem refm s∅ beh prefSp ((λ x sys → snd (pdecFp (e , x) sys))) pdecF n
-- -- -- -- refPTheorem {varsB = _} {_} {E ×ₚ PE} refm s∅ beh (rfPStA rfSt prefSp) pdecFp pdecF n ((e , pe) , left rst) | yes x , snd | r = {!!}
-- -- -- -- refPTheorem {varsB = _} {_} {E ×ₚ PE} refm s∅ beh (rfPStA rfSt prefSp) pdecFp pdecF n ((e , pe) , left rst) | no x , snd | r = unit , {!r pe!}
-- -- -- -- refPTheorem {PE = E ×ₚ PE} refm s∅ beh (rfPStA rfSt prefSp) pdecFp pdecF n ((e , pe) , right rst) = unit , right (cong refm rst)
-- -- -- -- refPTheorem {PE = .⊤ₚ} refm s∅ beh rf∅ pdecFp pdecF n (_ , left rst) = ⊥′-elim rst
-- -- -- -- refPTheorem {PE = .⊤ₚ} refm s∅ beh rf∅ pdecFp pdecF n (_ , right rst) = unit , right (cong refm rst)










-- -- -- -- -- -- TODO They are not needed , I think.
-- -- -- -- -- record RefActionCov {α n k} {varsA : Vec (Set α) (suc n)} {varsB : Vec (Set α) (suc k)}
-- -- -- -- --                     (refm : System varsB → System varsA) (actA : Action varsA) : Set (lsuc α) where
-- -- -- -- --   field
-- -- -- -- --     racts : List (RefAction {varsB = varsB} refm actA)
-- -- -- -- --     covering : (vs : System varsA) → (cnd : cond actA vs) → ∃ λ refAct → (refAct ∈ₗ racts) × ∃ (λ pvs → (cond (ract refAct) pvs) × refm pvs ≡ vs)


-- -- -- -- -- RefSpecCov : (refm : System {α} varsB → System {α} varsA) → (spec : Spec varsA m) → Set (lsuc α) 
-- -- -- -- -- RefSpecCov {varsB = varsB} refm (act ∷ []) = RefActionCov {varsB = varsB} refm act
-- -- -- -- -- RefSpecCov {varsB = varsB} refm (act ∷ spec@(_ ∷ _))
-- -- -- -- --   = RefActionCov {varsB = varsB} refm act × RefSpecCov {varsB = varsB} refm spec


-- -- -- -- -- 
