{-# OPTIONS --without-K --exact-split #-}

-- GuardG3.agda
-- Godel II with NON-TRIVIAL provability predicate via convergence semantics.
-- 0 postulates, 0 holes.

module GuardG3 where

open import ChwistekSyntax
  using (Nat; zero; suc; Code; catom; cnode; Eq; refl; eqCong)
open import TreeArith
  using (EmptyTA; SigmaTA; mkSigmaTA; UnitTA)
open import TreeArithTrack1
  using (CodeTm; ctVar; ctAtom; ctNode; ctCase; ctFold; ctEqNat; ctIf; ctEqCode;
         FormTA3; fbotTA3; fimpTA3; fallTA3; fexTA3; feqTA3;
         Env3; emptyEnv3; extendEnv3;
         evalCT; foldCT;
         GoodTA3; liftCode)
open import TreeArithInternal
  using (substCT; substF3;
         axK3; axS3; axRefl3; axSym3; axTrans3)
open import TreeArithBootstrap
  using (addB; tagMP3)
open import TreeArithGodel2
  using (encFormTA3)
open import GuardFull
  using (ProofG2; baseG2; mpG2; genG2; instG2; exIntroG2;
         checkCG2; ProvG2; encProofG2; proofFuelG2;
         checkerConvergeG2; d1G2; d2G2;
         foldEnvIndep; d2Semantic; checkerOnCatom)

------------------------------------------------------------------------
-- Section 1: Arithmetic
------------------------------------------------------------------------

private
  eqSym1 : {X : Set} {a b : X} -> Eq a b -> Eq b a
  eqSym1 refl = refl

  eqTrans1 : {X : Set} {a b c : X} -> Eq a b -> Eq b c -> Eq a c
  eqTrans1 refl q = q

  eqSubst1 : {A : Set} (P : A -> Set) {x y : A} -> Eq x y -> P x -> P y
  eqSubst1 P refl px = px

  addB-assoc : (a b c : Nat) -> Eq (addB (addB a b) c) (addB a (addB b c))
  addB-assoc zero    b c = refl
  addB-assoc (suc a) b c = eqCong suc (addB-assoc a b c)

  addB-suc-r : (x y : Nat) -> Eq (addB x (suc y)) (suc (addB x y))
  addB-suc-r zero    y = refl
  addB-suc-r (suc x) y = eqCong suc (addB-suc-r x y)

  addB-zero-r : (a : Nat) -> Eq (addB a zero) a
  addB-zero-r zero    = refl
  addB-zero-r (suc a) = eqCong suc (addB-zero-r a)

  addB-comm : (a b : Nat) -> Eq (addB a b) (addB b a)
  addB-comm zero    b = eqSym1 (addB-zero-r b)
  addB-comm (suc a) b =
    eqTrans1 (eqCong suc (addB-comm a b)) (eqSym1 (addB-suc-r b a))

  addB-comm-assoc : (f1 f2 g : Nat) ->
    Eq (addB (addB f1 f2) g) (addB f2 (addB f1 g))
  addB-comm-assoc f1 f2 g =
    eqTrans1 (eqCong (\ x -> addB x g) (addB-comm f1 f2))
             (addB-assoc f2 f1 g)

  addB-suc-r2 : (x g : Nat) ->
    Eq (addB x (suc (suc g))) (suc (suc (addB x g)))
  addB-suc-r2 x g = eqTrans1 (addB-suc-r x (suc g))
                      (eqCong suc (addB-suc-r x g))

------------------------------------------------------------------------
-- Section 2: liftCode convergence
------------------------------------------------------------------------

private
  eqCong2 : {A B C : Set} -> (f : A -> B -> C) -> {a1 a2 : A} -> {b1 b2 : B} ->
    Eq a1 a2 -> Eq b1 b2 -> Eq (f a1 b1) (f a2 b2)
  eqCong2 f refl refl = refl

liftCodeFuel : Code -> Nat
liftCodeFuel (catom _)   = suc zero
liftCodeFuel (cnode a b) = suc (addB (liftCodeFuel a) (liftCodeFuel b))

liftCodeConv : (c : Code) -> (env : Env3) -> (g : Nat) ->
  Eq (evalCT (addB (liftCodeFuel c) g) env (liftCode c)) c
liftCodeConv (catom n) env g = refl
liftCodeConv (cnode a b) env g =
  eqCong2 cnode (prf-a g) (prf-b g)
  where
  fa : Nat
  fa = liftCodeFuel a
  fb : Nat
  fb = liftCodeFuel b

  prf-a : (g : Nat) ->
    Eq (evalCT (addB (addB fa fb) g) env (liftCode a)) a
  prf-a g = eqSubst1
    (\ x -> Eq (evalCT x env (liftCode a)) a)
    (eqSym1 (addB-assoc fa fb g))
    (liftCodeConv a env (addB fb g))

  prf-b : (g : Nat) ->
    Eq (evalCT (addB (addB fa fb) g) env (liftCode b)) b
  prf-b g = eqSubst1
    (\ x -> Eq (evalCT x env (liftCode b)) b)
    (eqSym1 (addB-comm-assoc fa fb g))
    (liftCodeConv b env (addB fa g))

------------------------------------------------------------------------
-- Section 3: Convergence semantics
------------------------------------------------------------------------

ConvergeEq : Env3 -> CodeTm -> CodeTm -> Set
ConvergeEq env t1 t2 =
  SigmaTA Nat (\ f0 -> (g : Nat) -> Eq (evalCT (addB f0 g) env t1)
                                         (evalCT (addB f0 g) env t2))

GoodG3 : Env3 -> FormTA3 -> Set
GoodG3 env fbotTA3        = EmptyTA
GoodG3 env (fimpTA3 a b)  = GoodG3 env a -> GoodG3 env b
GoodG3 env (fallTA3 a)    = (c : Code) -> GoodG3 (extendEnv3 env c) a
GoodG3 env (fexTA3 a)     = SigmaTA Code (\ c -> GoodG3 (extendEnv3 env c) a)
GoodG3 env (feqTA3 t1 t2) = ConvergeEq env t1 t2

------------------------------------------------------------------------
-- Section 4: Proof system
------------------------------------------------------------------------

ProvG3 : FormTA3 -> FormTA3
ProvG3 A = fexTA3 (feqTA3 checkCG2 (liftCode (encFormTA3 A)))

data ProofG3 : FormTA3 -> Set where
  axKG : (A B : FormTA3) -> ProofG3 (fimpTA3 A (fimpTA3 B A))
  axSG : (A B C : FormTA3) ->
    ProofG3 (fimpTA3 (fimpTA3 A (fimpTA3 B C))
                      (fimpTA3 (fimpTA3 A B) (fimpTA3 A C)))
  mpG : {A B : FormTA3} -> ProofG3 (fimpTA3 A B) -> ProofG3 A -> ProofG3 B
  genG : {A : FormTA3} -> ProofG3 A -> ProofG3 (fallTA3 A)
  axReflG : (t : CodeTm) -> ProofG3 (feqTA3 t t)
  axSymG : (s t : CodeTm) ->
    ProofG3 (fimpTA3 (feqTA3 s t) (feqTA3 t s))
  axTransG : (r s t : CodeTm) ->
    ProofG3 (fimpTA3 (feqTA3 r s) (fimpTA3 (feqTA3 s t) (feqTA3 r t)))
  axD1G : {A : FormTA3} -> ProofG2 A -> ProofG3 (ProvG3 A)
  axD2G : {A B : FormTA3} ->
    ProofG3 (fimpTA3 (ProvG3 (fimpTA3 A B)) (fimpTA3 (ProvG3 A) (ProvG3 B)))

embed : {A : FormTA3} -> ProofG3 A -> ProofG2 A
embed (axKG A B)       = baseG2 (axK3 A B)
embed (axSG A B C)     = baseG2 (axS3 A B C)
embed (mpG pf pa)      = mpG2 (embed pf) (embed pa)
embed (genG p)         = genG2 (embed p)
embed (axReflG t)      = baseG2 (axRefl3 t)
embed (axSymG s t)     = baseG2 (axSym3 s t)
embed (axTransG r s t) = baseG2 (axTrans3 r s t)
embed (axD1G p)        = GuardFull.d1G2 p
embed (axD2G {A} {B})  = d2G2 {A} {B}

------------------------------------------------------------------------
-- Section 5: Soundness
------------------------------------------------------------------------

private
  catom-ne-cnode : {X : Set} -> (x y : Code) -> Eq (catom zero) (cnode x y) -> X
  catom-ne-cnode x y ()

soundG3 : {A : FormTA3} -> (env : Env3) -> ProofG3 A -> GoodG3 env A
soundG3 env (axKG A B)   = \ ha -> \ _ -> ha
soundG3 env (axSG A B C) = \ habc -> \ hab -> \ ha -> habc ha (hab ha)
soundG3 env (mpG pf pa)  = (soundG3 env pf) (soundG3 env pa)
soundG3 env (genG p)     = \ c -> soundG3 (extendEnv3 env c) p
soundG3 env (axReflG t) = mkSigmaTA zero (\ g -> refl)
soundG3 env (axSymG s t) = symConv
  where
  symConv : ConvergeEq env s t -> ConvergeEq env t s
  symConv (mkSigmaTA f0 prf) = mkSigmaTA f0 (\ g -> eqSym1 (prf g))
soundG3 env (axTransG r s t) = transConv
  where
  transConv : ConvergeEq env r s -> ConvergeEq env s t -> ConvergeEq env r t
  transConv (mkSigmaTA f1 prf1) (mkSigmaTA f2 prf2) =
    mkSigmaTA (addB f1 f2) (\ g ->
      eqTrans1
        (eqSubst1 (\ x -> Eq (evalCT x env r) (evalCT x env s))
          (eqSym1 (addB-assoc f1 f2 g)) (prf1 (addB f2 g)))
        (eqSubst1 (\ x -> Eq (evalCT x env s) (evalCT x env t))
          (eqSym1 (addB-comm-assoc f1 f2 g)) (prf2 (addB f1 g))))

-- D1 soundness
soundG3 env (axD1G {A} p) =
  mkSigmaTA (encProofG2 p) (mkSigmaTA f0 prfConv)
  where
  env' : Env3
  env' = extendEnv3 env (encProofG2 p)
  fChk : Nat
  fChk = suc (proofFuelG2 p)
  fLift : Nat
  fLift = liftCodeFuel (encFormTA3 A)

  f0 : Nat
  f0 = addB fChk fLift

  prfConv : (g : Nat) ->
    Eq (evalCT (addB f0 g) env' checkCG2)
       (evalCT (addB f0 g) env' (liftCode (encFormTA3 A)))
  prfConv g =
    eqTrans1 (chkStep g) (eqSym1 (liftStep g))
    where
    chkStep : (g : Nat) ->
      Eq (evalCT (addB (addB fChk fLift) g) env' checkCG2) (encFormTA3 A)
    chkStep g = eqSubst1
      (\ x -> Eq (evalCT x env' checkCG2) (encFormTA3 A))
      (eqSym1 (addB-assoc fChk fLift g))
      (checkerConvergeG2 p env (addB fLift g))

    liftStep : (g : Nat) ->
      Eq (evalCT (addB (addB fChk fLift) g) env' (liftCode (encFormTA3 A)))
         (encFormTA3 A)
    liftStep g = eqSubst1
      (\ x -> Eq (evalCT x env' (liftCode (encFormTA3 A))) (encFormTA3 A))
      (eqSym1 (addB-comm-assoc fChk fLift g))
      (liftCodeConv (encFormTA3 A) env' (addB fChk g))

-- D2 soundness
soundG3 env (axD2G {A} {B}) = \ provAB -> \ provA ->
  d2proof provAB provA
  where
  d2proof : GoodG3 env (ProvG3 (fimpTA3 A B)) ->
    GoodG3 env (ProvG3 A) ->
    GoodG3 env (ProvG3 B)

  -- Case 1: c1 = catom k. Contradiction.
  d2proof (mkSigmaTA (catom k) (mkSigmaTA f1 prf1))
          (mkSigmaTA c2 (mkSigmaTA f2 prf2)) =
    catom-contra k f1 prf1 c2 f2 prf2
    where
    catom-contra : (k : Nat) -> (f1 : Nat) ->
      ((g : Nat) -> Eq (evalCT (addB f1 g) (extendEnv3 env (catom k)) checkCG2)
                        (evalCT (addB f1 g) (extendEnv3 env (catom k))
                                (liftCode (encFormTA3 (fimpTA3 A B))))) ->
      (c2 : Code) -> (f2 : Nat) ->
      ((g : Nat) -> Eq (evalCT (addB f2 g) (extendEnv3 env c2) checkCG2)
                        (evalCT (addB f2 g) (extendEnv3 env c2)
                                (liftCode (encFormTA3 A)))) ->
      GoodG3 env (ProvG3 B)
    catom-contra k zero prf1 c2 f2 prf2 =
      catom-ne-cnode _ _
        (eqTrans1 (eqSym1 (checkerOnCatom k env fL))
          (eqTrans1 (prf1 (suc (suc fL)))
            (eqSubst1
              (\ x -> Eq (evalCT x env1 (liftCode (encFormTA3 (fimpTA3 A B))))
                          (encFormTA3 (fimpTA3 A B)))
              (eqSym1 arith-eq)
              (liftCodeConv (encFormTA3 (fimpTA3 A B)) env1 (suc (suc zero))))))
      where
      env1 : Env3
      env1 = extendEnv3 env (catom k)
      fL : Nat
      fL = liftCodeFuel (encFormTA3 (fimpTA3 A B))
      arith-eq : Eq (suc (suc fL)) (addB fL (suc (suc zero)))
      arith-eq = eqSym1 (eqTrans1 (addB-suc-r fL (suc zero))
                   (eqCong suc (eqTrans1 (addB-suc-r fL zero)
                     (eqCong suc (addB-zero-r fL)))))

    catom-contra k (suc f1') prf1 c2 f2 prf2 =
      catom-ne-cnode _ _
        (eqTrans1
          (eqSym1 (eqSubst1
            (\ x -> Eq (evalCT x env1 checkCG2) (catom zero))
            (eqSym1 (eqCong suc (addB-suc-r f1' fL)))
            (checkerOnCatom k env (addB f1' fL))))
          (eqTrans1 (prf1 (suc fL))
            (eqSubst1
              (\ x -> Eq (evalCT x env1 (liftCode (encFormTA3 (fimpTA3 A B))))
                          (encFormTA3 (fimpTA3 A B)))
              (eqSym1 arith-lift)
              (liftCodeConv (encFormTA3 (fimpTA3 A B)) env1 (suc (suc f1'))))))
      where
      env1 : Env3
      env1 = extendEnv3 env (catom k)
      fL : Nat
      fL = liftCodeFuel (encFormTA3 (fimpTA3 A B))
      arith-lift : Eq (suc (addB f1' (suc fL))) (addB fL (suc (suc f1')))
      arith-lift = eqTrans1
        (eqCong suc (eqTrans1 (addB-suc-r f1' fL) (eqCong suc (addB-comm f1' fL))))
        (eqSym1 (eqTrans1 (addB-suc-r fL (suc f1'))
                  (eqCong suc (addB-suc-r fL f1'))))

  -- Case 2: c1 = cnode la lb. Use d2Semantic.
  d2proof (mkSigmaTA (cnode la lb) (mkSigmaTA f1 prf1))
          (mkSigmaTA c2 (mkSigmaTA f2 prf2)) =
    d2-cnode la lb f1 prf1 c2 f2 prf2
    where
    d2-cnode : (la lb : Code) -> (f1 : Nat) ->
      ((g : Nat) -> Eq (evalCT (addB f1 g) (extendEnv3 env (cnode la lb)) checkCG2)
                        (evalCT (addB f1 g) (extendEnv3 env (cnode la lb))
                                (liftCode (encFormTA3 (fimpTA3 A B))))) ->
      (c2 : Code) -> (f2 : Nat) ->
      ((g : Nat) -> Eq (evalCT (addB f2 g) (extendEnv3 env c2) checkCG2)
                        (evalCT (addB f2 g) (extendEnv3 env c2)
                                (liftCode (encFormTA3 A)))) ->
      GoodG3 env (ProvG3 B)
    d2-cnode la lb f1 prf1 c2 f2 prf2 = assembleD2 d2raw
      where
      c1 : Code
      c1 = cnode la lb
      c3 : Code
      c3 = cnode (catom tagMP3) (cnode c1 c2)
      env1 : Env3
      env1 = extendEnv3 env c1
      env2 : Env3
      env2 = extendEnv3 env c2
      env3 : Env3
      env3 = extendEnv3 env c3

      fLiftAB : Nat
      fLiftAB = liftCodeFuel (encFormTA3 (fimpTA3 A B))
      fLiftA : Nat
      fLiftA = liftCodeFuel (encFormTA3 A)
      fLiftB : Nat
      fLiftB = liftCodeFuel (encFormTA3 B)

      -- Checker convergence at env1 to enc(A->B)
      chk1 : (g : Nat) ->
        Eq (evalCT (addB (addB f1 fLiftAB) g) env1 checkCG2) (encFormTA3 (fimpTA3 A B))
      chk1 g =
        eqTrans1
          (eqSubst1 (\ x -> Eq (evalCT x env1 checkCG2)
                                 (evalCT x env1 (liftCode (encFormTA3 (fimpTA3 A B)))))
            (eqSym1 (addB-assoc f1 fLiftAB g))
            (prf1 (addB fLiftAB g)))
          (eqSubst1 (\ x -> Eq (evalCT x env1 (liftCode (encFormTA3 (fimpTA3 A B))))
                                 (encFormTA3 (fimpTA3 A B)))
            (eqSym1 (addB-comm-assoc f1 fLiftAB g))
            (liftCodeConv (encFormTA3 (fimpTA3 A B)) env1 (addB f1 g)))

      -- Checker convergence at env2 to enc(A)
      chk2 : (g : Nat) ->
        Eq (evalCT (addB (addB f2 fLiftA) g) env2 checkCG2) (encFormTA3 A)
      chk2 g =
        eqTrans1
          (eqSubst1 (\ x -> Eq (evalCT x env2 checkCG2)
                                 (evalCT x env2 (liftCode (encFormTA3 A))))
            (eqSym1 (addB-assoc f2 fLiftA g))
            (prf2 (addB fLiftA g)))
          (eqSubst1 (\ x -> Eq (evalCT x env2 (liftCode (encFormTA3 A)))
                                 (encFormTA3 A))
            (eqSym1 (addB-comm-assoc f2 fLiftA g))
            (liftCodeConv (encFormTA3 A) env2 (addB f2 g)))

      -- Bump fuel by 2 so evalCT unfolds to foldCT
      ff1 : Nat
      ff1 = suc (addB f1 fLiftAB)

      fold1-env1 : (g : Nat) ->
        Eq (evalCT (suc (suc (addB (addB f1 fLiftAB) g))) env1 checkCG2)
           (encFormTA3 (fimpTA3 A B))
      fold1-env1 g = eqSubst1
        (\ x -> Eq (evalCT x env1 checkCG2) (encFormTA3 (fimpTA3 A B)))
        (addB-suc-r2 (addB f1 fLiftAB) g)
        (chk1 (suc (suc g)))

      ff2 : Nat
      ff2 = suc (addB f2 fLiftA)

      fold2-env2 : (g : Nat) ->
        Eq (evalCT (suc (suc (addB (addB f2 fLiftA) g))) env2 checkCG2)
           (encFormTA3 A)
      fold2-env2 g = eqSubst1
        (\ x -> Eq (evalCT x env2 checkCG2) (encFormTA3 A))
        (addB-suc-r2 (addB f2 fLiftA) g)
        (chk2 (suc (suc g)))

      -- Call d2Semantic. Its type uses foldCT ... acG2 ncG2.
      -- fold1-env1 g's type normalizes to foldCT (suc (addB (addB f1 fLiftAB) g)) env1 c1 acG2 ncG2 = enc(A->B).
      -- foldEnvIndep transfers from env1 to envX.
      -- d2Semantic : ... -> SigmaTA Nat (\ f3 -> ...)
      d2raw : SigmaTA Nat _
      d2raw = d2Semantic c1 c2 A B la lb refl ff1
        (\ envX g -> eqTrans1 (foldEnvIndep (addB ff1 g) envX env1 c1)
                               (fold1-env1 g))
        ff2
        (\ envX g -> eqTrans1 (foldEnvIndep (addB ff2 g) envX env2 c2)
                               (fold2-env2 g))

      -- Pattern-match to extract f3 and h3, then build the final ConvergeEq.
      assembleD2 : SigmaTA Nat
        (\ f3 -> (envX : Env3) -> (g : Nat) ->
          Eq (foldCT (addB f3 g) envX c3 _ _) (encFormTA3 B)) ->
        GoodG3 env (ProvG3 B)
      assembleD2 (mkSigmaTA f3 h3) = mkSigmaTA c3 (mkSigmaTA fOut prfOut)
        where
        fOut : Nat
        fOut = suc (suc (addB f3 fLiftB))

        -- Checker side: evalCT (addB fOut g) env3 checkCG2 = enc(B)
        -- addB fOut g = suc (suc (addB (addB f3 fLiftB) g)) [definitional]
        -- evalCT (suc (suc X)) env3 checkCG2 = foldCT (suc X) env3 c3 acG2 ncG2 [definitional]
        -- Need: foldCT (suc (addB (addB f3 fLiftB) g)) env3 c3 acG2 ncG2 = enc(B)
        -- = foldCT (addB f3 (suc (addB fLiftB g))) env3 c3 acG2 ncG2 = enc(B)
        -- by h3 env3 (suc (addB fLiftB g)) after arithmetic transport.
        chk-side : (g : Nat) ->
          Eq (evalCT (addB fOut g) env3 checkCG2) (encFormTA3 B)
        chk-side g =
          eqSubst1
            (\ x -> Eq (foldCT x env3 c3 _ _) (encFormTA3 B))
            (eqSym1 arith1)
            (h3 env3 (suc (addB fLiftB g)))
          where
          arith1 : Eq (suc (addB (addB f3 fLiftB) g)) (addB f3 (suc (addB fLiftB g)))
          arith1 = eqTrans1 (eqCong suc (addB-assoc f3 fLiftB g))
                     (eqSym1 (addB-suc-r f3 (addB fLiftB g)))

        -- LiftCode side: evalCT (addB fOut g) env3 (liftCode enc(B)) = enc(B)
        lift-side : (g : Nat) ->
          Eq (evalCT (addB fOut g) env3 (liftCode (encFormTA3 B))) (encFormTA3 B)
        lift-side g =
          eqSubst1
            (\ x -> Eq (evalCT x env3 (liftCode (encFormTA3 B)) ) (encFormTA3 B))
            (eqSym1 arith2)
            (liftCodeConv (encFormTA3 B) env3 (suc (suc (addB f3 g))))
          where
          arith2 : Eq (suc (suc (addB (addB f3 fLiftB) g)))
                       (addB fLiftB (suc (suc (addB f3 g))))
          arith2 = eqTrans1
            (eqCong suc (eqCong suc (addB-comm-assoc f3 fLiftB g)))
            (eqSym1 (eqTrans1 (addB-suc-r fLiftB (suc (addB f3 g)))
                      (eqCong suc (addB-suc-r fLiftB (addB f3 g)))))

        prfOut : (g : Nat) ->
          Eq (evalCT (addB fOut g) env3 checkCG2)
             (evalCT (addB fOut g) env3 (liftCode (encFormTA3 B)))
        prfOut g = eqTrans1 (chk-side g) (eqSym1 (lift-side g))

------------------------------------------------------------------------
-- Section 6: Consistency and D1/D2
------------------------------------------------------------------------

conG3 : ProofG3 fbotTA3 -> EmptyTA
conG3 p = soundG3 emptyEnv3 p

d1G3 : {A : FormTA3} -> ProofG3 A -> ProofG3 (ProvG3 A)
d1G3 p = axD1G (embed p)

d2G3 : {A B : FormTA3} -> ProofG3 (fimpTA3 (ProvG3 (fimpTA3 A B)) (fimpTA3 (ProvG3 A) (ProvG3 B)))
d2G3 = axD2G
