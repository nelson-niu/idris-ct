\iffalse
SPDX-License-Identifier: AGPL-3.0-only

This file is part of `idris-ct` Category Theory in Idris library.

Copyright (C) 2020 Stichting Statebox <https://statebox.nl>

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
\fi

> module CoLimits.CoProductAsFunctor
>
> import Basic.Category
> import Basic.Functor
> import Product.ProductCategory
> import CoLimits.CoProduct
> import Syntax.PreorderReasoning
>
> %access public export
> %default total
>
>
> coProductMapObj :
>      {cat : Category}
>   -> (coProduct : BinaryCoProduct cat)
>   -> (obj cat, obj cat)
>   -> obj cat
> coProductMapObj coProduct a = carrier $ coProduct (fst a) (snd a)
>
>
> coProductMapMor :
>      {cat : Category}
>   -> (coProduct : BinaryCoProduct cat)
>   -> (a, b : (obj cat, obj cat))
>   -> ProductMorphism cat cat a b
>   -> mor cat (carrier $ coProduct (fst a) (snd a))
>       (carrier $ coProduct (fst b) (snd b))
> coProductMapMor {cat} coProduct (la, ra) (lb, rb) (MkProductMorphism pi1 pi2)
>   = challenger $ exists
>       (coProduct la ra)
>       (carrier $ coProduct lb rb)
>       (compose cat la lb (carrier $ coProduct lb rb) pi1 $ inl (coProduct lb rb))
>       (compose cat ra rb (carrier $ coProduct lb rb) pi2 $ inr (coProduct lb rb))
>
>
> coProductPreserveId :
>      {cat : Category}
>   -> (coProduct : BinaryCoProduct cat)
>   -> (a : (obj cat, obj cat))
>   -> coProductMapMor {cat} coProduct a a (productIdentity a)
>    = identity cat (carrier $ coProduct (fst a) (snd a))
> coProductPreserveId {cat} coProduct (l, r) = sym prf where
>   coProd : CoProduct cat l r
>   coProd = coProduct l r
>
>   carr : obj cat
>   carr = carrier coProd
>   il : mor cat l carr
>   il = inl coProd
>   ir : mor cat r carr
>   ir = inr coProd
>
>   id : (c : obj cat) -> mor cat c c
>   id = identity cat
>
>   id_as_chall : CommutingMorphism cat l r carr carr il ir il ir
>   id_as_chall = MkCommutingMorphism (id carr)
>     (rightIdentity cat l carr il)
>     (rightIdentity cat r carr ir)
>
>   prf : id carr
>     = challenger $ exists
>         coProd carr
>         (compose cat l l carr (id l) il) -- = il
>         (compose cat r r carr (id r) ir) -- = ir
>   prf = rewrite (leftIdentity cat l carr il) in
>     rewrite (leftIdentity cat r carr ir) in
>     unique coProd carr il ir id_as_chall
>
>
> coProductPreserveCompose :
>      {cat : Category}
>   -> (coProduct : BinaryCoProduct cat)
>   -> (a, b, c : (obj cat, obj cat))
>   -> (f : ProductMorphism cat cat a b)
>   -> (g : ProductMorphism cat cat b c)
>   -> coProductMapMor {cat} coProduct a c
>       (compose (productCategory cat cat) a b c f g) =
>         compose cat
>                 (coProductMapObj {cat} coProduct a)
>                 (coProductMapObj {cat} coProduct b)
>                 (coProductMapObj {cat} coProduct c)
>                 (coProductMapMor {cat} coProduct a b f)
>                 (coProductMapMor {cat} coProduct b c g)
> coProductPreserveCompose {cat} coProduct (la, ra) (lb, rb) (lc, rc)
>   (MkProductMorphism lab rab) (MkProductMorphism lbc rbc) = sym prf where
>     coProda : CoProduct cat la ra
>     coProda = coProduct la ra
>     coProdb : CoProduct cat lb rb
>     coProdb = coProduct lb rb
>     coProdc : CoProduct cat lc rc
>     coProdc = coProduct lc rc
>
>     carra: obj cat
>     carra = carrier coProda
>     carrb: obj cat
>     carrb = carrier coProdb
>     carrc: obj cat
>     carrc = carrier coProdc
>
>     inla : mor cat la carra
>     inla = inl coProda
>     inra : mor cat ra carra
>     inra = inr coProda
>     inlb : mor cat lb carrb
>     inlb = inl coProdb
>     inrb : mor cat rb carrb
>     inrb = inr coProdb
>     inlc : mor cat lc carrc
>     inlc = inl coProdc
>     inrc : mor cat rc carrc
>     inrc = inr coProdc
>
>     comp : {x, y, z : obj cat} -> mor cat x y -> mor cat y z -> mor cat x z
>     comp {x} {y} {z} = compose cat x y z
>
>     lac : mor cat la lc
>     lac = comp {x=la} {y=lb} {z=lc} lab lbc
>     rac : mor cat ra rc
>     rac = comp {x=ra} {y=rb} {z=rc} rab rbc
>
>     commMorab : CommutingMorphism cat la ra carra carrb inla inra
>       (comp {x=la} {y=lb} {z=carrb} lab inlb)
>       (comp {x=ra} {y=rb} {z=carrb} rab inrb)
>     commMorab = exists coProda carrb
>       (comp {x=la} {y=lb} {z=carrb} lab inlb)
>       (comp {x=ra} {y=rb} {z=carrb} rab inrb)
>     commMorbc : CommutingMorphism cat lb rb carrb carrc inlb inrb
>       (comp {x=lb} {y=lc} {z=carrc} lbc inlc)
>       (comp {x=rb} {y=rc} {z=carrc} rbc inrc)
>     commMorbc = exists coProdb carrc
>       (comp {x=lb} {y=lc} {z=carrc} lbc inlc)
>       (comp {x=rb} {y=rc} {z=carrc} rbc inrc)
>     commMorac : CommutingMorphism cat la ra carra carrc inla inra
>       (comp {x=la} {y=lc} {z=carrc} lac inlc)
>       (comp {x=ra} {y=rc} {z=carrc} rac inrc)
>     commMorac = exists coProda carrc
>       (comp {x=la} {y=lc} {z=carrc} lac inlc)
>       (comp {x=ra} {y=rc} {z=carrc} rac inrc)
>
>     challab : mor cat carra carrb
>     challab = challenger commMorab
>     challbc : mor cat carrb carrc
>     challbc = challenger commMorbc
>     challac : mor cat carra carrc
>     challac = challenger commMorac
>
>     challabc : mor cat carra carrc
>     challabc = comp {x=carra} {y=carrb} {z=carrc} challab challbc
>
>     comp_as_chall : CommutingMorphism cat la ra carra carrc inla inra
>       (comp {x=la} {y=lc} {z=carrc} lac inlc)
>       (comp {x=ra} {y=rc} {z=carrc} rac inrc)
>     comp_as_chall = MkCommutingMorphism challabc commLeft commRight where
>       commLeft : comp {x=la} {y=carra} {z=carrc} inla challabc
>         = comp {x=la} {y=lc} {z=carrc} lac inlc
>       commLeft =
>         (comp inla challabc)
>           ={ associativity cat la carra carrb carrc inla challab challbc }=
>         (comp (comp inla challab) challbc)
>           ={ cong {f = \c => comp c challbc} $ commutativityLeft commMorab }=
>         (comp (comp lab inlb) challbc)
>           ={ sym $ associativity cat la lb carrb carrc lab inlb challbc }=
>         (comp lab (comp inlb challbc))
>           ={ cong $ commutativityLeft commMorbc }=
>         (comp lab (comp lbc inlc))
>           ={ associativity cat la lb lc carrc lab lbc inlc }=
>         (comp lac inlc)
>           QED
>
>       commRight : comp {x=ra} {y=carra} {z=carrc} inra challabc
>         = comp {x=ra} {y=rc} {z=carrc} rac inrc
>       commRight =
>         (comp inra challabc)
>           ={ associativity cat ra carra carrb carrc inra challab challbc }=
>         (comp (comp inra challab) challbc)
>           ={ cong {f = \c => comp c challbc} $ commutativityRight commMorab }=
>         (comp (comp rab inrb) challbc)
>           ={ sym $ associativity cat ra rb carrb carrc rab inrb challbc }=
>         (comp rab (comp inrb challbc))
>           ={ cong $ commutativityRight commMorbc }=
>         (comp rab (comp rbc inrc))
>           ={ associativity cat ra rb rc carrc rab rbc inrc }=
>         (comp rac inrc)
>           QED
>
>     prf : challabc = challac
>     prf = unique coProda carrc
>       (comp {x=la} {y=lc} {z=carrc} lac inlc)
>       (comp {x=ra} {y=rc} {z=carrc} rac inrc) comp_as_chall
>
>
> coProductAsFunctor :
>      {cat : Category}
>   -> BinaryCoProduct cat
>   -> CFunctor (productCategory cat cat) cat
> coProductAsFunctor coProduct = MkCFunctor
>   (coProductMapObj coProduct)
>   (coProductMapMor coProduct)
>   (coProductPreserveId coProduct)
>   (coProductPreserveCompose coProduct)
