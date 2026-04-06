{-# OPTIONS --safe --without-K --exact-split #-}

module Guard.ThFun where

open import Guard.Base
open import Guard.Term
open import Guard.Step

------------------------------------------------------------------------
-- Proof encoding tags

private
  n0  : Nat ; n0  = zero
  n1  : Nat ; n1  = suc n0
  n2  : Nat ; n2  = suc n1
  n3  : Nat ; n3  = suc n2
  n4  : Nat ; n4  = suc n3
  n5  : Nat ; n5  = suc n4
  n6  : Nat ; n6  = suc n5
  n7  : Nat ; n7  = suc n6
  n8  : Nat ; n8  = suc n7
  n9  : Nat ; n9  = suc n8
  n10 : Nat ; n10 = suc n9
  n11 : Nat ; n11 = suc n10
  n12 : Nat ; n12 = suc n11
  n13 : Nat ; n13 = suc n12
  n14 : Nat ; n14 = suc n13
  n15 : Nat ; n15 = suc n14
  n16 : Nat ; n16 = suc n15
  n17 : Nat ; n17 = suc n16
  n18 : Nat ; n18 = suc n17
  n19 : Nat ; n19 = suc n18
  n20 : Nat ; n20 = suc n19
  n21 : Nat ; n21 = suc n20
  n22 : Nat ; n22 = suc n21
  n23 : Nat ; n23 = suc n22
  n24 : Nat ; n24 = suc n23
  n25 : Nat ; n25 = suc n24

------------------------------------------------------------------------
-- Proof encodings
-- Convention: sub-proof always goes in the RIGHT child (position b).

encAxI     : Tree -> Tree
encAxI tC = nd (natCode n0) (nd tC lf)

encAxFst   : Tree -> Tree -> Tree
encAxFst aC bC = nd (natCode n1) (nd aC bC)

encAxSnd   : Tree -> Tree -> Tree
encAxSnd aC bC = nd (natCode n2) (nd aC bC)

encAxConst : Tree -> Tree -> Tree
encAxConst aC bC = nd (natCode n3) (nd aC bC)

encAxComp  : Tree -> Tree -> Tree -> Tree
encAxComp fC gC tC = nd (natCode n4) (nd fC (nd gC tC))

encAxComp2 : Tree -> Tree -> Tree -> Tree -> Tree
encAxComp2 hC fC gC tC = nd (natCode n5) (nd hC (nd fC (nd gC tC)))

encAxLift  : Tree -> Tree -> Tree -> Tree
encAxLift fC aC bC = nd (natCode n6) (nd fC (nd aC bC))

encAxPost  : Tree -> Tree -> Tree -> Tree -> Tree
encAxPost fC hC aC bC = nd (natCode n7) (nd fC (nd hC (nd aC bC)))

encAxFan   : Tree -> Tree -> Tree -> Tree -> Tree -> Tree
encAxFan h1C h2C hC aC bC = nd (natCode n8) (nd h1C (nd h2C (nd hC (nd aC bC))))

encAxRecLf : Tree -> Tree -> Tree
encAxRecLf zC sC = nd (natCode n9) (nd zC sC)

encAxRecNd : Tree -> Tree -> Tree -> Tree -> Tree
encAxRecNd zC sC aC bC = nd (natCode n10) (nd zC (nd sC (nd aC bC)))

encAxIfLfL : Tree -> Tree -> Tree
encAxIfLfL aC bC = nd (natCode n11) (nd aC bC)

encAxIfLfN : Tree -> Tree -> Tree -> Tree -> Tree
encAxIfLfN xC yC aC bC = nd (natCode n12) (nd xC (nd yC (nd aC bC)))

encAxTreeEqLL : Tree
encAxTreeEqLL = nd (natCode n13) lf

encAxTreeEqLN : Tree -> Tree -> Tree
encAxTreeEqLN aC bC = nd (natCode n14) (nd aC bC)

encAxTreeEqNL : Tree -> Tree -> Tree
encAxTreeEqNL aC bC = nd (natCode n15) (nd aC bC)

encAxTreeEqNN : Tree -> Tree -> Tree -> Tree -> Tree
encAxTreeEqNN a1C a2C b1C b2C = nd (natCode n16) (nd a1C (nd a2C (nd b1C b2C)))

encRefl : Tree -> Tree
encRefl tC = nd (natCode n17) (nd tC lf)

encSym : Tree -> Tree
encSym sp = nd (natCode n18) (nd tagVar sp)

encTrans : Tree -> Tree -> Tree
encTrans sp1 sp2 = nd (natCode n19) (nd sp1 sp2)

-- cong1 f sp: a=fCode, b=sp (sub-proof in right child)
encCong1 : Tree -> Tree -> Tree
encCong1 fC sp = nd (natCode n20) (nd fC sp)

-- congL g x sp: a=nd(gCode,xCode), b=sp
encCongL : Tree -> Tree -> Tree -> Tree
encCongL gC xC sp = nd (natCode n21) (nd (nd gC xC) sp)

-- congR g x sp: a=nd(gCode,xCode), b=sp
encCongR : Tree -> Tree -> Tree -> Tree
encCongR gC xC sp = nd (natCode n22) (nd (nd gC xC) sp)

-- ruleInst x t sp: a=nd(tCode,xNatCode), b=sp
-- Note: tCode first to ensure intermediate passthrough (code t is always nd,
-- so reify is Pair-tagged, avoiding natCode collision when x=0, t=O).
encInst : Tree -> Tree -> Tree -> Tree
encInst tC xC sp = nd (natCode n23) (nd (nd tC xC) sp)

-- ruleF f g z s bf sf bg sg: a=nd(fCode,gCode), b=nd(nd(zCode,sCode),nd(nd(sp1,sp2),nd(sp3,sp4)))
encF : Tree -> Tree -> Tree -> Tree -> Tree -> Tree -> Tree -> Tree -> Tree
encF fC gC zC sC sp1 sp2 sp3 sp4 = nd (natCode n24) (nd (nd fC gC) (nd (nd zC sC) (nd (nd sp1 sp2) (nd sp3 sp4))))

-- axKT: a=tCode, b=xCode
encAxKT : Tree -> Tree -> Tree
encAxKT tC xC = nd (natCode n25) (nd tC xC)

------------------------------------------------------------------------
-- codeEqn : Equation -> Tree

codeEqn : Equation -> Tree
codeEqn (eqn l r) = nd (code l) (code r)

------------------------------------------------------------------------
-- Functor code tag abbreviations (offset 26)
private
  f0  : Nat ; f0  = suc n25           -- 26: I / Pair
  f1  : Nat ; f1  = suc f0            -- 27: Fst / Const
  f2  : Nat ; f2  = suc f1            -- 28: Snd / Lift
  f3  : Nat ; f3  = suc f2            -- 29: Comp / Post
  f4  : Nat ; f4  = suc f3            -- 30: Comp2 / Fan
  f5  : Nat ; f5  = suc f4            -- 31: Rec / IfLf
  f6  : Nat ; f6  = suc f5            -- 32: KT / TreeEq

------------------------------------------------------------------------
-- Helper: coded functor constructors
private
  codeRec : Tree -> Tree -> Tree
  codeRec zC sC = nd (natCode f5) (nd zC sC)

  codeKT : Tree -> Tree
  codeKT tC = nd (natCode f6) tC

  codeComp : Tree -> Tree -> Tree
  codeComp fC gC = nd (natCode f3) (nd fC gC)

  codeComp2 : Tree -> Tree -> Tree -> Tree
  codeComp2 hC fC gC = nd (natCode f4) (nd hC (nd fC gC))

  codeLift : Tree -> Tree
  codeLift fC = nd (natCode f2) fC

  codePost : Tree -> Tree -> Tree
  codePost fC hC = nd (natCode f3) (nd fC hC)

  codeFan : Tree -> Tree -> Tree -> Tree
  codeFan h1C h2C hC = nd (natCode f4) (nd h1C (nd h2C hC))

  oC : Tree
  oC = nd tagO lf

  pairC : Tree
  pairC = codeF2 Pair

  iflfC : Tree
  iflfC = codeF2 IfLf

  treeeqC : Tree
  treeeqC = codeF2 TreeEq

  oneC : Tree
  oneC = mkAp2 pairC oC oC

  var0C : Tree
  var0C = nd tagVar lf

------------------------------------------------------------------------
-- thFun : Tree -> Tree

thFun : Tree -> Tree
thFun lf = lf
thFun (nd tag lf) =
  boolCase (treeEq tag (natCode n13))
    (nd (mkAp2 treeeqC oC oC) oC)
    lf
thFun (nd tag (nd a b)) = thD tag a b (thFun a) (thFun b)
  where
  thD : Tree -> Tree -> Tree -> Tree -> Tree -> Tree
  -- axI: a=tC, b=lf
  thD tag a b ra rb =
   boolCase (treeEq tag (natCode n0))
    (nd (mkAp1 (codeF1 I) a) a)
   (boolCase (treeEq tag (natCode n1))
    (nd (mkAp1 (codeF1 Fst) (mkAp2 pairC a b)) a)
   (boolCase (treeEq tag (natCode n2))
    (nd (mkAp1 (codeF1 Snd) (mkAp2 pairC a b)) b)
   (boolCase (treeEq tag (natCode n3))
    (nd (mkAp2 (codeF2 Const) a b) a)
   (boolCase (treeEq tag (natCode n4))
    (nd (mkAp1 (codeComp a (leftT b)) (rightT b))
        (mkAp1 a (mkAp1 (leftT b) (rightT b))))
   (boolCase (treeEq tag (natCode n5))
    (nd (mkAp1 (codeComp2 a (leftT b) (leftT (rightT b))) (rightT (rightT b)))
        (mkAp2 a (mkAp1 (leftT b) (rightT (rightT b)))
                 (mkAp1 (leftT (rightT b)) (rightT (rightT b)))))
   (boolCase (treeEq tag (natCode n6))
    (nd (mkAp2 (codeLift a) (leftT b) (rightT b))
        (mkAp1 a (leftT b)))
   (boolCase (treeEq tag (natCode n7))
    (nd (mkAp2 (codePost a (leftT b)) (leftT (rightT b)) (rightT (rightT b)))
        (mkAp1 a (mkAp2 (leftT b) (leftT (rightT b)) (rightT (rightT b)))))
   (boolCase (treeEq tag (natCode n8))
    (nd (mkAp2 (codeFan a (leftT b) (leftT (rightT b)))
               (leftT (rightT (rightT b))) (rightT (rightT (rightT b))))
        (mkAp2 (leftT (rightT b))
               (mkAp2 a (leftT (rightT (rightT b))) (rightT (rightT (rightT b))))
               (mkAp2 (leftT b) (leftT (rightT (rightT b))) (rightT (rightT (rightT b))))))
   (boolCase (treeEq tag (natCode n9))
    (nd (mkAp1 (codeRec a b) oC) a)
   (boolCase (treeEq tag (natCode n10))
    (nd (mkAp1 (codeRec a (leftT b))
               (mkAp2 pairC (leftT (rightT b)) (rightT (rightT b))))
        (mkAp2 (leftT b)
               (mkAp2 pairC (leftT (rightT b)) (rightT (rightT b)))
               (mkAp2 pairC (mkAp1 (codeRec a (leftT b)) (leftT (rightT b)))
                            (mkAp1 (codeRec a (leftT b)) (rightT (rightT b))))))
   (boolCase (treeEq tag (natCode n11))
    (nd (mkAp2 iflfC oC (mkAp2 pairC a b)) a)
   (boolCase (treeEq tag (natCode n12))
    (nd (mkAp2 iflfC (mkAp2 pairC a (leftT b))
                     (mkAp2 pairC (leftT (rightT b)) (rightT (rightT b))))
        (rightT (rightT b)))
   (boolCase (treeEq tag (natCode n14))
    (nd (mkAp2 treeeqC oC (mkAp2 pairC a b)) oneC)
   (boolCase (treeEq tag (natCode n15))
    (nd (mkAp2 treeeqC (mkAp2 pairC a b) oC) oneC)
   (boolCase (treeEq tag (natCode n16))
    (nd (mkAp2 treeeqC (mkAp2 pairC a (leftT b))
                       (mkAp2 pairC (leftT (rightT b)) (rightT (rightT b))))
        (mkAp2 iflfC (mkAp2 treeeqC a (leftT (rightT b)))
                     (mkAp2 pairC (mkAp2 treeeqC (leftT b) (rightT (rightT b))) oneC)))
   (boolCase (treeEq tag (natCode n17))
    (nd a a)
   (boolCase (treeEq tag (natCode n18))
    (nd (rightT rb) (leftT rb))
   (boolCase (treeEq tag (natCode n19))
    (nd (leftT ra) (rightT rb))
   (boolCase (treeEq tag (natCode n20))
    (nd (mkAp1 a (leftT rb)) (mkAp1 a (rightT rb)))
   (boolCase (treeEq tag (natCode n21))
    (nd (mkAp2 (leftT a) (leftT rb) (rightT a))
        (mkAp2 (leftT a) (rightT rb) (rightT a)))
   (boolCase (treeEq tag (natCode n22))
    (nd (mkAp2 (leftT a) (rightT a) (leftT rb))
        (mkAp2 (leftT a) (rightT a) (rightT rb)))
   (boolCase (treeEq tag (natCode n23))
    (nd (codedSubst (leftT a) (rightT a) (leftT rb))
        (codedSubst (leftT a) (rightT a) (rightT rb)))
   (boolCase (treeEq tag (natCode n24))
    (nd (mkAp1 (leftT a) var0C) (mkAp1 (rightT a) var0C))
   (boolCase (treeEq tag (natCode n25))
    (nd (mkAp1 (codeKT a) b) a)
   lf))))))))))))))))))))))))
