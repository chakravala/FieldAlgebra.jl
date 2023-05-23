
#   This file is part of FieldAlgebra.jl
#   It is licensed under the MIT license
#   FieldAlgebra Copyright (C) 2022 Michael Reed
#       _           _                         _
#      | |         | |                       | |
#   ___| |__   __ _| | ___ __ __ ___   ____ _| | __ _
#  / __| '_ \ / _` | |/ / '__/ _` \ \ / / _` | |/ _` |
# | (__| | | | (_| |   <| | | (_| |\ V / (_| | | (_| |
#  \___|_| |_|\__,_|_|\_\_|  \__,_| \_/ \__,_|_|\__,_|
#
#   https://github.com/chakravala
#   https://crucialflow.com

struct Field{G,T,S,N,M} <: AbstractModule
    v::Values{M,Values{N,T}}
    c::Values{M,S}
    @pure function Field{G,T,S,N,M}(v,c) where {G,T,S,N,M}
        r = promoteints(FieldConstants.cache.(c))
        new{G,T,eltype(r),N,M}(v,r)
    end
    @pure function Field{G,T,S,N,M}(v,c) where {G,T<:Rational,S,N,M}
        r,p = promoteints(v),promoteints(FieldConstants.cache.(c))
        new{G,eltype(r),eltype(p),N,M}(r,p)
    end
    @pure function Field{G,T,S,N,M}(v::Values{T,N},c) where {G,T<:Rational,S,N,M}
        r,p = promoteints(v),promoteints(FieldConstants.cache.(c))
        new{G,eltype(r),eltype(p),N,M}(r,p)
    end
end

Base.:+(a::Group{G,T,S,N},b::Group{G,T,S,N}) where {G,T,S,N} = a.v≠b.v ? Field{G,T,S,N,2}(Values(a.v,b.v),Values(a.c,b.c)) : Field{G,T,S,N,1}(Values((a.v,)),Values(a.c+b.c))
Base.:-(a::Group{G,T,S,N},b::Group{G,T,S,N}) where {G,T,S,N} = a.v≠b.v ? Field{G,T,S,N,2}(Values(a.v,b.v),Values(a.c,-b.c)) : Field{G,T,S,N,1}(Values((a.v,),Values(a.c-b.c)))

function Base.:+(a::Field{G,T,S,N,M},b::Group{G,T,S,N}) where {G,T,S,N,M}
    j = findfirst(z->z==b.v,a.v)
    if isnothing(j)
        Field{G,T,S,N,M+1}(Values(a.v...,b.v),Values(a.c...,b.c))
    else
        Field{G,T,S,N,M}(a.v,Values(a.c[1:j-1]...,a.c[j]+b.c,a.c[j+1:end]...))
    end
end
function Base.:-(a::Field{G,T,S,N,M},b::Group{G,T,S,N}) where {G,T,S,N,M}
    j = findfirst(z->z==b.v,a.v)
    if isnothing(j)
        Field{G,T,S,N,M+1}(Values(a.v...,b.v),Values(a.c...,-b.c))
    else
        Field{G,T,S,N,M}(a.v,Values(a.c[1:j-1]...,a.c[j]-b.c,a.c[j+1:end]...))
    end
end

function Base.:+(a::Group{G,T,S,N},b::Field{G,T,S,N,M}) where {G,T,S,N,M}
    j = findfirst(z->z==a.v,b.v)
    if isnothing(j)
        Field{G,T,S,N,M+1}(Values(a.v,b.v...),Values(a.c,b.c...))
    else
        Field{G,T,S,N,M}(a.v,Values(b.c[1:j-1]...,a.c+b.c[j],b.c[j+1:end]...))
    end
end
function Base.:-(a::Group{G,T,S,N},b::Field{G,T,S,N,M}) where {G,T,S,N,M}
    j = findfirst(z->z==a.v,b.v)
    if isnothing(j)
        Field{G,T,S,N,M+1}(Values(a.v,b.v...),Values(a.c,-b.c...))
    else
        Field{G,T,S,N,M}(b.v,Values(-b.c[1:j-1]...,a.c-b.c[j],-b.c[j+1:end]...))
    end
end

function Base.:+(a::Field{G,T,S,N,M},b::Field{G,T,S,N,L}) where {G,T,S,N,M,L}
    j = findall(z->z∈a.v,b.v)
    jj = [findfirst(z->z==b.v[i],a.v) for i ∈ j]
    if isempty(j)
        Field{G,T,S,N,M+L}(Values(a.v...,b.v...),Values(a.c...,b.c...))
    else
        c = Variables(a.c)
        c[jj] += b.c[j]
        jjj = [i for i ∈ 1:L if i∉j]
        Field{G,T,S,N,M+L-length(j)}(Values(a.v...,b.v[jjj]...),Values(c...,b.c[jjj]...))
    end
end
function Base.:-(a::Field{G,T,S,N,M},b::Field{G,T,S,N,L}) where {G,T,S,N,M,L}
    j = findall(z->z∈b.v,a.v)
    jj = [findfirst(z->z==b.v[i],a.v) for i ∈ j]
    if isempty(j)
        Field{G,T,S,N,M+L}(Values(a.v...,b.v...),Values(a.c...,-b.c...))
    else
        c = Variables(a.c)
        c[jj] -= b.c[j]
        jjj = [i for i ∈ 1:L if i∉j]
        Field{G,T,S,N,M+L-length(j)}(Values(a.v...,b.v[jjj]...),Values(c...,-b.c[jjj]...))
    end
end

function Base.show(io::IO,p::Field{G,T,S,N,M}) where {G,T,S,N,M}
    show(io,Group{G,T,S,N}(p.v[1],p.c[1]))
    for i ∈ 2:M
        if !iszero(p.c[i])
            print(io," + ")
            show(io,Group{G,T,S,N}(p.v[i],p.c[i]))
        end
    end
end
