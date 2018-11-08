module TLA.Refine where

open import TLA.Def

open import Prelude.List hiding ([_])

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
    range-embed : (vs : System varsB) → (nvs : System varsB) → (cnd : cond ract vs)
                  → (cndA : cond actA (refm vs)) → (rsp : resp ract vs cnd nvs)
                  → resp actA (refm vs) cndA (refm nvs)
open RefAction public


PRefAction : (B : Set α) → (refm : System {α} varsB → System {α} varsA) → (actA : Action varsA) → Set (lsuc α)
PRefAction {varsB = varsB} B refm actA = (b : B) → RefAction {varsB = varsB} refm actA


record RefPAction {α n k} {varsA : Vec (Set α) (suc n)} {varsB : Vec (Set α) (suc k)}
                 {B : Set α} (refm : System varsB → System varsA) (pactA : PAction B varsA) : Set (lsuc α) where
  field
    par : System varsB → B
    ract : Action varsB
    dom-embed : (vs : System varsB) → (cnd : cond ract vs) → cond (pactA (par vs)) (refm vs)
    range-embed : (vs : System varsB) → (nvs : System varsB) → (cnd : cond ract vs)
                  → (cndA : cond (pactA (par vs)) (refm vs)) → (rsp : resp ract vs cnd nvs)
                  → resp (pactA (par vs)) (refm vs) cndA (refm nvs)
open RefPAction public


PRefPAction : (E : Set α) → (refm : System {α} varsB → System {α} varsA) → (pactA : PAction B varsA)
             → Set (lsuc α)
PRefPAction {varsB = varsB} E refm pactA = (b : E) → RefPAction {varsB = varsB} refm pactA


record RefStAction {α n k} {varsA : Vec (Set α) (suc n)} {varsB : Vec (Set α) (suc k)}
                 (refm : System varsB → System varsA) : Set (lsuc α) where
  field
    ract : Action varsB
    isConst : (vs : System varsB) → (nvs : System varsB) → (cnd : cond ract vs)
              → (rsp : resp ract vs cnd nvs)
              → refm vs ≡ refm nvs
open RefStAction public

PRefStAction : (B : Set α) → (refm : System {α} varsB → System {α} varsA)
               → Set (lsuc α)
PRefStAction {varsA = varsA} {varsB = varsB} B refm = (b : B) → RefStAction {varsA = varsA} {varsB = varsB} refm


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
refTheorem refm (act ∷ spec) beh (ract ∷ rs , refSp) decFp decF n (left (left rst)) | yes dra , sndra | g | yes da , snda = left (left (range-embed ract (beh n) (beh (suc n)) dra da rst))
refTheorem refm (act ∷ spec) beh (ract ∷ rs , refSp) decFp decF n (left (right rst)) | yes dra , sndra | g | yes da , snda = g (left rst)
refTheorem refm (act ∷ spec) beh (ract ∷ rs , refSp) decFp decF n (left rst) | yes dra , sndra | g | no da , snda =  ⊥-elim (da (dom-embed ract (beh n) dra))
refTheorem refm (act ∷ spec) beh (ract ∷ rs , refSp) decFp decF n (left rst) | no dra , sndra | g = g (left rst)



-- Terminating is used here for the rfpA case.
{-# TERMINATING #-}
exPSp : {refm : System varsB → System varsA} → (gref : GRefSpec {varsA = varsA} {varsB = varsB} refm PE gspec)
        → GSpec varsB PE
exPSp (rfA ref) = gsp (exSp ref) s∅
exPSp (prfStA refSt gref) =
  let cind = exPSp gref
  in gsp (gToSpec cind) (spPA (λ e → ract (refSt e)) (gToPSpec cind))
exPSp (prfA prefA ind) =
  let cind = either exPSp exPSp ind
  in gsp (gToSpec cind) (spPA (λ e → ract (prefA e)) (gToPSpec cind))
exPSp (rfpA refPA ind) =
  let cind = either exPSp exPSp ind
  in gsp (ract refPA ∷ gToSpec cind) (gToPSpec cind)
exPSp (prfpA prefPA ind) =
  let cind = either exPSp exPSp ind
  in gsp (gToSpec cind) (spPA (λ e → ract (prefPA e)) (gToPSpec cind))
  


refPTheorem : (refm : System varsB → System varsA) → (gspec : GSpec varsA PB) → (beh : (System varsB)ʷ)
              → (gref : GRefSpec {varsB = varsB} refm PE gspec) → (gdecFp : GDecF PE (exPSp gref)) → (gdecF : GDecF PB gspec)
              → [ GTRestr PE (exPSp gref) beh gdecFp ⇒ GTRestr PB gspec ( ⟨ refm ⟩ $ʷ beh ) gdecF ]

-- Proving it for the simple case where we do not have parametrized Actions. Using the above theorem.
refPTheorem refm (gsp spec s∅) beh (rfA ref) gdecFp gdecF n (left rst) = left (refTheorem refm spec beh ref (fst gdecFp) (fst gdecF) n rst)

-- This is unnecessary complexity. (but probably unavoidable).
refPTheorem refm .(gsp _ s∅) beh (rfA ref) gdecFp gdecF n (right (_ , left empty)) = ⊥′-elim empty
refPTheorem refm .(gsp _ s∅) beh (rfA ref) gdecFp gdecF n (right (_ , right eq)) = right (unit , right (cong refm eq))

refPTheorem refm .(gsp _ s∅) beh (prfStA refSt gref) gdecFp gdecF n rst = {!!}
refPTheorem refm .(gsp (_ ∷ _) s∅) beh (prfA prefA ind) gdecFp gdecF n rst = {!!}
refPTheorem refm .(gsp _ (spPA _ _)) beh (rfpA refPA ind) gdecFp gdecF n rst = {!!}
refPTheorem refm .(gsp _ (spPA _ _)) beh (prfpA prefPA ind) gdecFp gdecF n rst = {!!}



-- refPLemma2 : (refm : System varsB → System varsA) → (beh : (System varsB)ʷ)
--               → (prefSp : GRefSpec {varsA = varsA} {varsB = varsB} refm PE s∅) → (pdecFp : PDecF PE (exPSp prefSp))
--               → [ PTRestr PE (exPSp prefSp) beh pdecFp ⇒ PTRestr {vars = varsA} ⊤ₚ s∅ ( ⟨ refm ⟩ $ʷ beh ) (λ b sys → unit) ]
-- refPLemma2 refm beh (rfStA rfSt prefSp) pdecFp n rst = {!!}
-- refPLemma2 refm beh (rfPStA rfSt prefSp) pdecFp n rst = {!!}
-- refPLemma2 refm beh rf∅ pdecFp n (_ , left rst) = ⊥′-elim rst
-- refPLemma2 refm beh rf∅ pdecFp n (_ , right rst) = unit , right (cong refm rst)

-- refPTheorem2 : (refm : System varsB → System varsA) → (pspec : PSpec varsA PB) → (beh : (System varsB)ʷ)
--               → (prefSp : GRefSpec {varsB = varsB} refm PE pspec) → (pdecFp : PDecF PE (exPSp prefSp)) → (pdecF : PDecF PB pspec)
--               → [ PTRestr PE (exPSp prefSp) beh pdecFp ⇒ PTRestr PB pspec ( ⟨ refm ⟩ $ʷ beh ) pdecF ]
-- refPTheorem2 refm (spA act pspec) beh prefSp pdecFp pdecF n rst = {!!}
-- refPTheorem2 refm (spPA pact pspec) beh prefSp pdecFp pdecF n rst = {!!}
-- refPTheorem2 {PE = PE} refm s∅ beh prefSp pdecFp pdecF = refPLemma2 refm beh prefSp pdecFp


-- refPTheorem : (refm : System varsB → System varsA) → (pspec : PSpec varsA PB) → (beh : (System varsB)ʷ)
--               → (prefSp : GRefSpec {varsB = varsB} refm PE pspec) → (pdecFp : PDecF PE (exPSp prefSp)) → (pdecF : PDecF PB pspec)
--               → [ PTRestr PE (exPSp prefSp) beh pdecFp ⇒ PTRestr PB pspec ( ⟨ refm ⟩ $ʷ beh ) pdecF ]
-- refPTheorem refm (spA act pspec) beh prefSp pdecFp pdecF n rst = {!!}
-- refPTheorem refm (spPA pact pspec) beh prefSp pdecFp pdecF n rst = {!!}
-- refPTheorem {PE = PE} refm s∅ beh (rfStA rfSt prefSp) pdecFp pdecF n rst = {!!}
-- refPTheorem {PE = E ×ₚ PE} refm s∅ beh (rfPStA rfSt prefSp) pdecFp pdecF n ((e , pe) , left rst) with pdecFp (e , pe) (beh n) | refPTheorem refm s∅ beh prefSp ((λ x sys → snd (pdecFp (e , x) sys))) pdecF n
-- refPTheorem {varsB = _} {_} {E ×ₚ PE} refm s∅ beh (rfPStA rfSt prefSp) pdecFp pdecF n ((e , pe) , left rst) | yes x , snd | r = {!!}
-- refPTheorem {varsB = _} {_} {E ×ₚ PE} refm s∅ beh (rfPStA rfSt prefSp) pdecFp pdecF n ((e , pe) , left rst) | no x , snd | r = unit , {!r pe!}
-- refPTheorem {PE = E ×ₚ PE} refm s∅ beh (rfPStA rfSt prefSp) pdecFp pdecF n ((e , pe) , right rst) = unit , right (cong refm rst)
-- refPTheorem {PE = .⊤ₚ} refm s∅ beh rf∅ pdecFp pdecF n (_ , left rst) = ⊥′-elim rst
-- refPTheorem {PE = .⊤ₚ} refm s∅ beh rf∅ pdecFp pdecF n (_ , right rst) = unit , right (cong refm rst)










-- -- -- TODO They are not needed , I think.
-- -- record RefActionCov {α n k} {varsA : Vec (Set α) (suc n)} {varsB : Vec (Set α) (suc k)}
-- --                     (refm : System varsB → System varsA) (actA : Action varsA) : Set (lsuc α) where
-- --   field
-- --     racts : List (RefAction {varsB = varsB} refm actA)
-- --     covering : (vs : System varsA) → (cnd : cond actA vs) → ∃ λ refAct → (refAct ∈ₗ racts) × ∃ (λ pvs → (cond (ract refAct) pvs) × refm pvs ≡ vs)


-- -- RefSpecCov : (refm : System {α} varsB → System {α} varsA) → (spec : Spec varsA m) → Set (lsuc α) 
-- -- RefSpecCov {varsB = varsB} refm (act ∷ []) = RefActionCov {varsB = varsB} refm act
-- -- RefSpecCov {varsB = varsB} refm (act ∷ spec@(_ ∷ _))
-- --   = RefActionCov {varsB = varsB} refm act × RefSpecCov {varsB = varsB} refm spec


-- -- 
