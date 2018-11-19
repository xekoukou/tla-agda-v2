module TLA.Refine2 where

open import TLA.Def2 public




variable
  refm : System varsB → System varsA

record RefAction {α n k} {varsA : VSet {α} n} {varsB : VSet {α} k}
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



record RefPAction {α n k} {varsA : VSet {α} n} {varsB : VSet {α} k}
                 {B : Set α} (refm : System varsB → System varsA) (pactA : PAction B varsA) : Set (lsuc α) where
  field
    par : System varsB → B
    ract : Action varsB
    dom-embed : (vs : System varsB) → (cnd : cond ract vs) → cond (pactA (par vs)) (refm vs)
    range-embed : (vs : System varsB) → (nvs : System varsB)
                  → (cnd : cond ract vs) → (rsp : resp ract vs nvs)
                  → resp (pactA (par vs)) (refm vs) (refm nvs)
open RefPAction public



PRefPAction : (E : Set α) → (refm : System {α} varsB → System {α} varsA) → (pactA : PAction B varsA)
             → Set (lsuc α)
PRefPAction {varsB = varsB} E refm pactA = (b : E) → RefPAction {varsB = varsB} refm pactA



record RefStAction {α n k} {varsA : VSet {α} n} {varsB : VSet {α} k}
                 (refm : System varsB → System varsA) : Set (lsuc α) where
  field
    ract : Action varsB
    isConst : (sys : System varsB) → (nsys : System varsB) → (cnd : cond ract sys)
              → (rsp : resp ract sys nsys)
              → refm sys ≡ refm nsys
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


extractSpec : {refm : System varsB → System varsA} → RefSpec {varsA = varsA} {varsB = varsB} refm spec → Spec varsB
extractSpec {spec = []} rsp = map ract rsp
extractSpec {spec = act ∷ spec} (lra , rsp) =  (map ract lra) ++ extractSpec rsp




data GRefSpec {α n k varsA varsB} (refm : System {α} {k} varsB → System {α} {n} varsA)
              : ∀{en bn PB} (PE : PSet {α} en) (gspec : GSpec {k = bn} varsA PB) → Set (lsuc α) where
  rf    : (ref : RefSpec {varsA = varsA} {varsB = varsB} refm spec)
          → GRefSpec refm ⊤ₚ (gsp spec psp∅)
  pst_∷_ : (refSt : PRefStAction {varsA = varsA} {varsB = varsB} E refm)
          → (gref : GRefSpec {varsA = varsA} {varsB = varsB} refm PE (gsp spec psp∅))
          → GRefSpec refm (E ×ₚ PE) (gsp spec psp∅)
  prf_∷_   : ∀{actA spec} → (prefA : PRefAction {varsA = varsA} {varsB = varsB} E refm actA)
          → let indf x = GRefSpec {varsA = varsA} {varsB = varsB} refm PE (gsp x psp∅)
            in (gref : indf (actA ∷ spec) ⊎ indf spec)
          → GRefSpec refm (E ×ₚ PE) (gsp (actA ∷ spec) psp∅)
  rfp_∷_   : (refPA : RefPAction {varsA = varsA} {varsB = varsB} refm pact)
          → let indf z y x = GRefSpec {varsB = varsB} refm {bn = z} {PB = y} PE (gsp spec x)
            in (gref : indf (suc m) (B ×ₚ PB) (pact +psp+ pspec) ⊎ indf m PB pspec)
          → GRefSpec refm PE (gsp spec (_+psp+_ {B = B} {PB = PB} pact pspec))
  prfp_∷_  : (prefPA : PRefPAction {varsA = varsA} {varsB = varsB} E refm pact)
          → let indf z y x = GRefSpec {varsB = varsB} refm {bn = z} {PB = y} PE (gsp spec x)
            in (gref : indf (suc m) (B ×ₚ PB) (_+psp+_ pact pspec) ⊎ indf m PB pspec)
          → GRefSpec refm {PB = (B ×ₚ PB)} (E ×ₚ PE) (gsp spec (_+psp+_ pact pspec))



_addSt_ : {refm : System {α} varsB → System {α} varsA} → {spec : Spec varsA}
        → RefSpec {varsB = varsB} refm spec → RefStAction {varsA = varsA} {varsB = varsB} refm
        → RefSpec {varsB = varsB} refm spec
_addSt_ {spec = []} ref rfa = rfa ∷ ref
_addSt_ {spec = act ∷ spec} (rfas , ind) rfa = rfas , (ind addSt rfa)


-- Do not use this.
extractGSpec : {refm : System varsB → System varsA}
               → (gref : GRefSpec {varsA = varsA} {varsB = varsB} refm {PB = PB} PE gspec)
               → GSpec varsB PE
extractGSpec (rf ref) = gsp (extractSpec ref) psp∅
extractGSpec (pst refSt ∷ gref)
  = let ind = extractGSpec gref
    in gsp (sp ind) ((λ e → ract (refSt e)) +psp+ (psp ind))
extractGSpec (prf prefA ∷ (gref ←u))
  = let ind = extractGSpec gref
    in gsp (sp ind) (((λ e → ract (prefA e)) +psp+ (psp ind)))
extractGSpec (prf prefA ∷ (u→ gref))
  = let ind = extractGSpec gref
    in gsp (sp ind) (((λ e → ract (prefA e)) +psp+ (psp ind)))
extractGSpec (rfp refPA ∷ (gref ←u))
  = let ind = extractGSpec gref
    in gsp (ract refPA ∷ (sp ind)) (psp ind)
extractGSpec (rfp refPA ∷ (u→ gref))
  = let ind = extractGSpec gref
    in gsp (ract refPA ∷ (sp ind)) (psp ind)
extractGSpec (prfp prefPA ∷ (gref ←u))
  = let ind = extractGSpec gref
    in gsp (sp ind) (((λ e → ract (prefPA e)) +psp+ (psp ind)))
extractGSpec (prfp prefPA ∷ (u→ gref))
  = let ind = extractGSpec gref
    in gsp (sp ind) (((λ e → ract (prefPA e)) +psp+ (psp ind)))

-- Maybe this is wrong. We need all the spec. We could have a limited version
-- bu would require knowledge of rst.
gextrSpec : {refm : System varsB → System varsA}
             → (gref : GRefSpec {varsA = varsA} {varsB = varsB} refm {PB = PB} PE gspec)
             → (pe : pStoUS PE)
             → Spec varsB
gextrSpec {PE = ⊤ₚ} (rf ref) pe = extractSpec ref
gextrSpec {PE = ⊤ₚ} (rfp refPA ∷ (gref ←u)) pe = ract refPA ∷ gextrSpec gref unit
gextrSpec {PE = ⊤ₚ} (rfp refPA ∷ (u→ gref)) pe = ract refPA ∷ gextrSpec gref unit
gextrSpec {PE = E ×ₚ PE} (pst refSt ∷ gref) (e ←u) = ract (refSt e) ∷ []
gextrSpec {PE = E ×ₚ PE} (pst refSt ∷ gref) (u→ pe) = gextrSpec gref pe
gextrSpec {PE = E ×ₚ PE} (prf prefA ∷ (gref ←u)) (e ←u) = ract (prefA e) ∷ [] 
gextrSpec {PE = E ×ₚ PE} (prf prefA ∷ (gref ←u)) (u→ pe) = gextrSpec gref pe
gextrSpec {PE = E ×ₚ PE} (prf prefA ∷ (u→ gref)) (e ←u) = ract (prefA e) ∷ []
gextrSpec {PE = E ×ₚ PE} (prf prefA ∷ (u→ gref)) (u→ pe) = gextrSpec gref pe
-- Here depending on the pe, we might add more actions than neccessary.
-- Is it possible to simplify this ? Probably not.
gextrSpec {PE = E ×ₚ PE} (rfp refPA ∷ (gref ←u)) pe = ract refPA ∷ gextrSpec gref pe
gextrSpec {PE = E ×ₚ PE} (rfp refPA ∷ (u→ gref)) pe = ract refPA ∷ gextrSpec gref pe
gextrSpec {PE = E ×ₚ PE} (prfp prefPA ∷ (gref ←u)) (e ←u) = ract (prefPA e) ∷ [] 
gextrSpec {PE = E ×ₚ PE} (prfp prefPA ∷ (gref ←u)) (u→ pe) = gextrSpec gref pe
gextrSpec {PE = E ×ₚ PE} (prfp prefPA ∷ (u→ gref)) (e ←u) = ract (prefPA e) ∷ [] 
gextrSpec {PE = E ×ₚ PE} (prfp prefPA ∷ (u→ gref)) (u→ pe) = gextrSpec gref pe
