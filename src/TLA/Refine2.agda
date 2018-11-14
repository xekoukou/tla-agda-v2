module TLA.Refine2 where

open import TLA.Def2 public




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



PRefAction : (B : Set α) → (refm : System {α} varsB → System {α} varsA) → (actA : Action varsA) → Set (lsuc α)
PRefAction {varsB = varsB} B refm actA = (b : B) → RefAction {varsB = varsB} refm actA



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



PRefPAction : (E : Set α) → (refm : System {α} varsB → System {α} varsA) → (pactA : PAction B varsA)
             → Set (lsuc α)
PRefPAction {varsB = varsB} E refm pactA = (b : E) → RefPAction {varsB = varsB} refm pactA



record RefStAction {α} {varsA : PSet α} {varsB : PSet α}
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


