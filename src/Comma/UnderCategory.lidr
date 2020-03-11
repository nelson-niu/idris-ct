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

> module Slice.UnderCategory
>
> import Basic.Category
> import Basic.Functor
> import Comma.CommaCategory
> import Unit.UnitCategory
>
> %access public export
> %default total
>
> underCategory : obj cat -> Category
> underCategory {cat} x = commaCategory (functorFromUnit x) (idFunctor cat)
>
> underObject : (x, y : obj cat) -> (f : mor cat x y) -> obj (underCategory x)
> underObject x y f = MkCommaObject () y f
