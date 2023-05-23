# FieldAlgebra.jl

*Field algebra based on Group design*

[![DOI](https://zenodo.org/badge/538546202.svg)](https://zenodo.org/badge/latestdoi/538546202)
[![Build status](https://ci.appveyor.com/api/projects/status/p8yu8cth0eoctd54?svg=true)](https://ci.appveyor.com/project/chakravala/fieldalgebra-jl)

Work in progress of abelian `Group` implementation which is extended to `Field` algebra.
```Julia
julia> @ring xyz x y z

julia> x*y^2
xy²

julia> ans/x
y²

julia> x+y^2
x + y²
```
There are more undocumented features which will be explained once the design matures.

Fundamental principle of design is to construct `Field` algebra from an abelian `Group` algebra construction built on a vector space module.

Used in [Similitude.jl](https://github.com/chakravala/Similitude.jl) and [MeasureSystems.jl](https://github.com/chakravala/MeasureSystems.jl) to implement dimensional group algebra.
