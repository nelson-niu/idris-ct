module MonoidalCategory.CoCartesianMonoidalCategory

import Basic.Category
-- import Basic.Functor
-- import Basic.NaturalIsomorphism
-- import Basic.NaturalTransformation
-- import Product.ProductCategory
-- import Product.ProductFunctor
import CoLimits.InitialObject
import CoLimits.CoProduct
-- import Utils
import MonoidalCategory.MonoidalCategory

%access public export
%default total

-- A category with finite coproducts forms a (symmetric) monoidal category.



CoCartesianMonoidalCategory :
     (cat : Category)
  -> (coProduct : (l, r : obj cat) -> CoProduct cat l r)
  -> (initObj : InitialObject cat)
  -> MonoidalCategory
CoCartesianMonoidalCategory cat coProduct initObj = ?CoCartesianMonoidalCategory_rhs
