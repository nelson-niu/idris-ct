module CoLimits.CoProduct

import Basic.Category
import Basic.Isomorphism

%access public export
%default total
%auto_implicits off

record ArbitraryCommutingMorphism
  (index : Type) (cat : Category)
  (diagram : index -> obj cat) (carrier : obj cat) (c : obj cat)
  (inj : (i : index) -> mor cat (diagram i) carrier)
  (f : (i : index) -> mor cat (diagram i) c)
where
  constructor MkArbitraryCommutingMorphism
  challenger : mor cat carrier c
  commutativity :
       (i : index)
    -> compose cat (diagram i) carrier c (inj i) challenger = f i

record ArbitraryCoProduct
  (index : Type) (cat : Category) (diagram : index -> obj cat)
where
  constructor MkArbitraryCoProduct
  carrier : obj cat
  inj : (i : index) -> mor cat (diagram i) carrier
  exists :
       (c : obj cat)
    -> (f : (i : index) -> mor cat (diagram i) c)
    -> ArbitraryCommutingMorphism index cat diagram carrier c inj f
  unique :
       (c : obj cat)
    -> (f : (i : index) -> mor cat (diagram i) c)
    -> (h : ArbitraryCommutingMorphism index cat diagram carrier c inj f)
    -> challenger h = challenger (exists c f)

arbitraryCoProductMorphism :
     (index : Type)
  -> (cat : Category)
  -> (diagram : index -> obj cat)
  -> (a, b : ArbitraryCoProduct index cat diagram)
  -> ArbitraryCommutingMorphism
      index cat diagram
      (carrier a) (carrier b)
      (inj a) (inj b)
arbitraryCoProductMorphism index cat diagram a b = exists a (carrier b) (inj b)

composeArbitraryCoProductMorphisms :
     (index : Type)
  -> (cat : Category)
  -> (diagram : index -> obj cat)
  -> (a, b : ArbitraryCoProduct index cat diagram)
  -> ArbitraryCommutingMorphism
      index cat diagram
      (carrier a) (carrier a)
      (inj a) (inj a)
composeArbitraryCoProductMorphisms index cat diagram a b =
 let
   mor = arbitraryCoProductMorphism index cat diagram a b
   inv = arbitraryCoProductMorphism index cat diagram b a
 in
   MkArbitraryCommutingMorphism
     (compose cat (carrier a) (carrier b) (carrier a)
       (challenger mor) (challenger inv))
     (\i => rewrite associativity cat (diagram i) (carrier a) (carrier b)
              (carrier a) (inj a i) (challenger mor) (challenger inv) in
            rewrite commutativity mor i in
            rewrite commutativity inv i in Refl)

idArbitraryCommutingMorphism :
     (index : Type)
  -> (cat : Category)
  -> (diagram : index -> obj cat)
  -> (a : ArbitraryCoProduct index cat diagram)
  -> ArbitraryCommutingMorphism
       index cat diagram
       (carrier a) (carrier a)
       (inj a) (inj a)
idArbitraryCommutingMorphism index cat diagram a = MkArbitraryCommutingMorphism
  (identity cat (carrier a))
  (\i => rightIdentity cat (diagram i) (carrier a) (inj a i))

arbitraryCoProductsAreIsomorphic :
     (index : Type)
  -> (cat : Category)
  -> (diagram : index -> obj cat)
  -> (a, b : ArbitraryCoProduct index cat diagram)
  -> Isomorphic cat (carrier a) (carrier b)
arbitraryCoProductsAreIsomorphic index cat diagram a b =
  let
    mor = arbitraryCoProductMorphism index cat diagram a b
    inv = arbitraryCoProductMorphism index cat diagram b a
  in
    buildIsomorphic
     (challenger mor)
     (challenger inv)
     (rewrite unique a (carrier a) (inj a)
                  (composeArbitraryCoProductMorphisms index cat diagram a b) in
      rewrite unique a (carrier a) (inj a)
                  (idArbitraryCommutingMorphism index cat diagram a) in Refl)
     (rewrite unique b (carrier b) (inj b)
                  (composeArbitraryCoProductMorphisms index cat diagram b a) in
      rewrite unique b (carrier b) (inj b)
                  (idArbitraryCommutingMorphism index cat diagram b) in Refl)

record CommutingMorphism
  (cat : Category)
  (l : obj cat) (r : obj cat) (carrier : obj cat) (c : obj cat)
  (inl : mor cat l carrier) (inr : mor cat r carrier)
  (f : mor cat l c) (g : mor cat r c)
where
  constructor MkCommutingMorphism
  challenger         : mor cat carrier c
  commutativityLeft  : compose cat l carrier c inl challenger = f
  commutativityRight : compose cat r carrier c inr challenger = g

  -- (index : Type) (cat : Category)
  -- (diagram : index -> obj cat) (carrier : obj cat) (c : obj cat)
  -- (inj : (i : index) -> mor cat (diagram i) carrier)
  -- (f : (i : index) -> mor cat (diagram i) c)




bool : {a : Type} -> {P : a -> Type} -> {l, r : a}
  -> P l -> P r -> (p : Bool) -> P (if p then l else r)
bool x y True = x
bool x y False = y

-- bool3 : {a, b, c : Type} -> {P : a -> b -> c -> Type}
--   -> {la, ra : a} -> {lb, rb : b} -> {lc, rc : c}
--   -> P la lb lc -> P ra rb rc -> (p : Bool)
--   -> P (if p then la else ra) (if p then lb else rb) (if p then lc else rc)
-- bool3 x y True = x
-- bool3 x y False = y

toBoolCommutingMorphism :
     {cat : Category}
  -> {l, r, carrier, c : obj cat}
  -> {inl : mor cat l carrier}
  -> {inr : mor cat r carrier}
  -> {f : mor cat l c}
  -> {g : mor cat r c}
  -> CommutingMorphism cat l r carrier c inl inr f g
  -> ArbitraryCommutingMorphism Bool cat (\p => if p then l else r) carrier c
       (bool {P = \d => mor cat d carrier} inl inr)
       (bool {P = \d => mor cat d c} f g)
toBoolCommutingMorphism {cat} {l} {r} {carrier} {c} {inl} {inr} {f} {g}
  (MkCommutingMorphism challenger commutativityLeft commutativityRight)
    = MkArbitraryCommutingMorphism challenger commutativity where
        commutativity : (p : Bool) -> compose cat (if p then l else r)
          carrier c (bool {P = \d => mor cat d carrier} inl inr p)
          challenger = bool {P = \d => mor cat d c} f g p
        commutativity True = commutativityLeft
        commutativity False = commutativityRight

-- fromBoolCommutingMorphism :
--      {cat : Category}
--   -> {l, r, carrier, c : obj cat}
--   -> {inl : mor cat l carrier}
--   -> {inr : mor cat r carrier}
--   -> {f : mor cat l c}
--   -> {g : mor cat r c}
--   -> CommutingMorphism cat l r carrier c inl inr f g
--   -> ArbitraryCommutingMorphism Bool cat (\p => if p then l else r) carrier c
--        (bool {P = \d => mor cat d carrier} inl inr)
--        (bool {P = \d => mor cat d c} f g)
-- toArbitraryCommutingMorphism {cat} {l} {r} {carrier} {c} {inl} {inr} {f} {g}
--   (MkCommutingMorphism challenger commutativityLeft commutativityRight)
--     = MkArbitraryCommutingMorphism challenger commutativity where
--         commutativity : (p : Bool) -> compose cat (if p then l else r)
--           carrier c (bool {P = \d => mor cat d carrier} inl inr p)
--           challenger = bool {P = \d => mor cat d c} f g p
--         commutativity True = commutativityLeft
--         commutativity False = commutativityRight


record CoProduct
  (cat : Category)
  (l : obj cat) (r : obj cat)
where
  constructor MkCoProduct
  carrier: obj cat
  inl: mor cat l carrier
  inr: mor cat r carrier
  exists:
       (c : obj cat)
    -> (f : mor cat l c)
    -> (g : mor cat r c)
    -> CommutingMorphism cat l r carrier c inl inr f g
  unique:
       (c : obj cat)
    -> (f : mor cat l c)
    -> (g : mor cat r c)
    -> (h : CommutingMorphism cat l r carrier c inl inr f g)
    -> challenger h = challenger (exists c f g)

toBoolCoProduct :
     {cat : Category}
  -> {l, r : obj cat}
  -> CoProduct cat l r
  -> ArbitraryCoProduct Bool cat (\p => if p then l else r)
toBoolCoProduct {cat} {l} {r} (MkCoProduct carrier inl inr exists unique)
  = MkArbitraryCoProduct carrier inj exists2 unique2 where
      inj : (p : Bool) -> mor cat (if p then l else r) carrier
      inj = bool {P = \d => mor cat d carrier} inl inr

      exists2 :
           (c : obj cat)
        -> (f : (p : Bool) -> mor cat (if p then l else r) c)
        -> ArbitraryCommutingMorphism Bool cat (\p => if p then l else r)
             carrier c inj f

      exists2' :
           (c : obj cat)
        -> (f : (p : Bool) -> mor cat (if p then l else r) c)
        -> ArbitraryCommutingMorphism Bool cat (\p => if p then l else r)
             carrier c inj
             (bool {P = \d => mor cat d c} (f True) (f False))
      exists2' c f = toBoolCommutingMorphism $ exists c (f True) (f False)

      unique2 :
           (c : obj cat)
        -> (f : (p : Bool) -> mor cat (if p then l else r) c)
        -> (h : ArbitraryCommutingMorphism Bool cat (\p => if p then l else r)
             carrier c inj f)
        -> challenger h = challenger (exists2 c f)
      unique2 c f h = ?unique2_rhs


-- toBoolCommutingMorphism :
--      {cat : Category}
--   -> {l, r, carrier, c : obj cat}
--   -> {inl : mor cat l carrier}
--   -> {inr : mor cat r carrier}
--   -> {f : mor cat l c}
--   -> {g : mor cat r c}
--   -> CommutingMorphism cat l r carrier c inl inr f g
--   -> ArbitraryCommutingMorphism Bool cat (\p => if p then l else r) carrier c
--        (bool {P = \d => mor cat d carrier} inl inr)
--        (bool {P = \d => mor cat d c} f g)
-- toBoolCommutingMorphism {cat} {l} {r} {carrier} {c} {inl} {inr} {f} {g}
--   (MkCommutingMorphism challenger commutativityLeft commutativityRight)
--     = MkArbitraryCommutingMorphism challenger commutativity where
--         commutativity : (p : Bool) -> compose cat (if p then l else r)
--           carrier c (bool {P = \d => mor cat d carrier} inl inr p)
--           challenger = bool {P = \d => mor cat d c} f g p
--         commutativity True = commutativityLeft
--         commutativity False = commutativityRight



-- carrier : obj cat
-- inj : (i : index) -> mor cat (diagram i) carrier
-- exists :
--      (c : obj cat)
--   -> (f : (i : index) -> mor cat (diagram i) c)
--   -> ArbitraryCommutingMorphism index cat diagram carrier c inj f
-- unique :
--      (c : obj cat)
--   -> (f : (i : index) -> mor cat (diagram i) c)
--   -> (h : ArbitraryCommutingMorphism index cat diagram carrier c inj f)
--   -> challenger h = challenger (exists c f)

 --
 -- coProductMorphism :
 --      (cat : Category)
 --   -> (l, r : obj cat)
 --   -> (a, b : CoProduct cat l r)
 --   -> CommutingMorphism
 --        cat
 --        l r (carrier a) (carrier b)
 --        (inl a) (inr a)
 --        (inl b) (inr b)
 -- coProductMorphism = arbitraryCoProductMorphism
 --
 -- composeCoProductMorphisms :
 --      (cat : Category)
 --   -> (l, r : obj cat)
 --   -> (a, b : CoProduct cat l r)
 --   -> CommutingMorphism
 --        cat
 --        l r (carrier a) (carrier a)
 --        (inl a) (inr a)
 --        (inl a) (inr a)
 -- composeCoProductMorphisms cat l r a b =
 --   let
 --     mor = coProductMorphism cat l r a b
 --     inv = coProductMorphism cat l r b a
 --   in
 --     MkCommutingMorphism
 --       (compose cat (carrier a) (carrier b) (carrier a)
 --         (challenger mor) (challenger inv))
 --       (rewrite associativity cat l (carrier a) (carrier b) (carrier a)
 --                (inl a) (challenger mor) (challenger inv) in
 --        rewrite commutativityLeft mor in
 --        rewrite commutativityLeft inv in Refl)
 --       (rewrite associativity cat r (carrier a) (carrier b) (carrier a)
 --                (inr a) (challenger mor) (challenger inv) in
 --        rewrite commutativityRight mor in
 --        rewrite commutativityRight inv in Refl)
 --
 -- idCommutingMorphism :
 --      (cat : Category)
 --   -> (l, r : obj cat)
 --   -> (a : CoProduct cat l r)
 --   -> CommutingMorphism
 --        cat
 --        l r (carrier a) (carrier a)
 --        (inl a) (inr a)
 --        (inl a) (inr a)
 -- idCommutingMorphism cat l r a = MkCommutingMorphism
 --   (identity cat (carrier a))
 --   (rightIdentity cat l (carrier a) (inl a))
 --   (rightIdentity cat r (carrier a) (inr a))
 --
 -- coProductsAreIsomorphic :
 --      (cat : Category)
 --   -> (l, r : obj cat)
 --   -> (a, b : CoProduct cat l r)
 --   -> Isomorphic cat (carrier a) (carrier b)
 -- coProductsAreIsomorphic cat l r a b =
 --   let
 --     mor = coProductMorphism cat l r a b
 --     inv = coProductMorphism cat l r b a
 --   in
 --     buildIsomorphic
 --       (challenger mor)
 --       (challenger inv)
 --       (rewrite unique a (carrier a) (inl a) (inr a)
 --                         (composeCoProductMorphisms cat l r a b) in
 --        rewrite unique a (carrier a) (inl a) (inr a)
 --                         (idCommutingMorphism cat l r a) in Refl)
 --       (rewrite unique b (carrier b) (inl b) (inr b)
 --                         (composeCoProductMorphisms cat l r b a) in
 --        rewrite unique b (carrier b) (inl b) (inr b)
 --                         (idCommutingMorphism cat l r b) in Refl)
