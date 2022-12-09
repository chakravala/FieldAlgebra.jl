# FieldAlgebra.jl

*Field algebra based on Group design*

[![DOI](https://zenodo.org/badge/538546202.svg)](https://zenodo.org/badge/latestdoi/538546202)
[![Build status](https://ci.appveyor.com/api/projects/status/p8yu8cth0eoctd54?svg=true)](https://ci.appveyor.com/project/chakravala/fieldalgebra-jl)

Work in progress of `Group` implementation which will also be extended to field algebra.
```Julia
julia> @group xyz x y z

julia> x*y^2
xy²

julia> ans/x
y²
```
There are more undocumented features which will be explained once the design matures.

Used in [Similitude.jl](https://github.com/chakravala/Similitude.jl) and [MeasureSystems.jl](https://github.com/chakravala/MeasureSystems.jl) to implement dimensional group algebra.
