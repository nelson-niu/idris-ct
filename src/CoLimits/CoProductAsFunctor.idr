module CoLimits.CoProductAsFunctor

import Basic.Category
import Basic.Functor
import Product.ProductCategory
import CoLimits.CoProduct

%access public export
%default total
%auto_implicits off

-- Coproducts yield functors.

coProductMapObj :
     (cat : Category)
  -> (coProduct : ((l, r : obj cat) -> CoProduct cat l r))
  -> (obj cat, obj cat)
  -> obj cat
coProductMapObj cat coProduct (l, r) = carrier $ coProduct l r

coProductMapMor :
     (cat : Category)
  -> (coProduct : ((l, r : obj cat) -> CoProduct cat l r))
  -> (a, b : (obj cat, obj cat))
  -> ProductMorphism cat cat a b
  -> mor cat (carrier $ coProduct (fst a) (snd a))
      (carrier $ coProduct (fst b) (snd b))
coProductMapMor cat coProduct (la, ra) (lb, rb) (MkProductMorphism pi1 pi2)
  = challenger $ exists
      (coProduct la ra)
      (carrier $ coProduct lb rb)
      (compose cat la lb (carrier $ coProduct lb rb) pi1 $ inl (coProduct lb rb))
      (compose cat ra rb (carrier $ coProduct lb rb) pi2 $ inr (coProduct lb rb))

coProductPreserveId :
     (cat : Category)
  -> (coProduct : ((l, r : obj cat) -> CoProduct cat l r))
  -> (a : (obj cat, obj cat))
  -> coProductMapMor cat coProduct a a (productIdentity a)
   = identity cat (carrier $ coProduct (fst a) (snd a))


coProductPreserveCompose :
     (cat : Category)
  -> (coProduct : ((l, r : obj cat) -> CoProduct cat l r))
  -> (a : obj (productCategory cat cat))
  -> (b : obj (productCategory cat cat))
  -> (c : obj (productCategory cat cat))
  -> (f : mor (productCategory cat cat) a b)
  -> (g : mor (productCategory cat cat) b c)
  -> coProductMapMor cat coProduct a c (compose (productCategory cat cat) a b c f g) =
      compose cat
              (coProductMapObj cat coProduct a)
              (coProductMapObj cat coProduct b)
              (coProductMapObj cat coProduct c)
              (coProductMapMor cat coProduct a b f)
              (coProductMapMor cat coProduct b c g)


  -- -> (a, b, c : (obj cat, obj cat))
  -- -> (f : ProductMorphism cat cat a b)
  -- -> (g : ProductMorphism cat cat b c)
  -- -> coProductMapMor cat coProduct a c (productCompose a b c f g)
  --  = compose cat (carrier $ coProduct (fst a) (snd a))
  --     (carrier $ coProduct (fst b) (snd b))
  --     (carrier $ coProduct (fst c) (snd c))
  --     (coProductMapMor cat coProduct a b f)
  --     (coProductMapMor cat coProduct b c g)


coProductAsFunctor :
     (cat : Category)
  -> ((l, r : obj cat) -> CoProduct cat l r)
  -> CFunctor (productCategory cat cat) cat
coProductAsFunctor cat coProduct = MkCFunctor
  (\(l, r) => carrier $ coProduct l r)
  (coProductMapMor cat coProduct)
  (coProductPreserveId cat coProduct)
  (coProductPreserveCompose cat coProduct)
