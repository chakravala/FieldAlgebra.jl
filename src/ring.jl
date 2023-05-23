
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

export Ring

struct Ring{G,T,S,N,M} <: AbstractModule
    v::Values{M,Values{N,T}}
    c::Values{M,S}
    @pure function Ring{G,T,S,N,M}(v,c) where {G,T,S,N,M}
        r = promoteints(FieldConstants.cache.(c))
        new{G,T,eltype(r),N,M}(v,r)
    end
    @pure function Ring{G,T,S,N,M}(v,c) where {G,T<:Rational,S,N,M}
        r,p = promoteints(v),promoteints(FieldConstants.cache.(c))
        new{G,eltype(r),eltype(p),N,M}(r,p)
    end
    @pure function Ring{G,T,S,N,M}(v::Values{T,N},c) where {G,T<:Rational,S,N,M}
        r,p = promoteints(v),promoteints(FieldConstants.cache.(c))
        new{G,eltype(r),eltype(p),N,M}(r,p)
    end
end

Ring(g::Group{G,T,S,N}) where {G,T,S,N} = Ring{G,T,S,N,1}(Values((g.v,)),Values(g.c))

Base.signbit(::Ring) = false

Base.zero(::Type{Ring{G,T,S,N}}) where {G,T,S,N} = Ring{G,T,S,N,0}(Values{0,Values{N,T}}(),Values{0,S}())
Base.zero(::Ring{G,T,S,N}) where {G,T,S,N} = Ring{G,T,S,N,0}(Values{0,Values{N,T}}(),Values{0,S}())
Base.one(::Type{Ring{G,T,S,N}}) where {G,T,S,N} = Ring{G,T,S,N,1}(Values{1,Values{N,T}}(),Values{1,S}())
Base.one(::Ring{G,T,S,N}) where {G,T,S,N} = Ring{G,T,S,N,1}(Values{1,Values{N,T}}((zeros(Values{N,T}),)),Values{1,S}(1))

(f::Ring{G,T,S,N,M})(v::Values{N}) where {G,T,S,N,M} = sum([prod(v.^f.v[i]) for i ∈ 1:M])

Base.:-(f::Ring{G,T,S,N,M}) where {G,T,S,N,M} = Ring{G,T,S,N,M}(f.v,-f.c)

Base.:+(a::Group{G,T,S,N},b::Group{G,T,S,N}) where {G,T,S,N} = a.v≠b.v ? Ring{G,T,S,N,2}(Values(a.v,b.v),Values(a.c,b.c)) : Ring{G,T,S,N,1}(Values((a.v,)),Values(a.c+b.c))
Base.:-(a::Group{G,T,S,N},b::Group{G,T,S,N}) where {G,T,S,N} = a.v≠b.v ? Ring{G,T,S,N,2}(Values(a.v,b.v),Values(a.c,-b.c)) : Ring{G,T,S,N,1}(Values((a.v,),Values(a.c-b.c)))

function Base.:+(a::Ring{G,T,S,N,M},b::Group{G,T,S,N}) where {G,T,S,N,M}
    j = findfirst(z->z==b.v,a.v)
    if isnothing(j)
        Ring{G,T,S,N,M+1}(Values((a.v...,b.v)),Values(a.c...,b.c))
    else
        c = a.c[j]+b.c
        if iszero(c)
            if iszero(M-1)
                zero(Ring{G,T,S,N})
            else
                Ring{G,T,S,N,M-1}(Values((a.v[1:j-1]...,a.v[j+1:end]...)),Values(a.c[1:j-1]...,a.c[j+1:end]...))
            end
        else
            Ring{G,T,S,N,M}(a.v,Values(a.c[1:j-1]...,c,a.c[j+1:end]...))
        end
    end
end
function Base.:-(a::Ring{G,T,S,N,M},b::Group{G,T,S,N}) where {G,T,S,N,M}
    j = findfirst(z->z==b.v,a.v)
    if isnothing(j)
        Ring{G,T,S,N,M+1}(Values((a.v...,b.v)),Values(a.c...,-b.c))
    else
        c = a.c[j]-b.c
        if iszero(c)
            if iszero(M-1)
                zero(Ring{G,T,S,N})
            else
                Ring{G,T,S,N,M-1}(Values((a.v[1:j-1]...,a.v[j+1:end]...)),Values(a.c[1:j-1]...,a.c[j+1:end]...))
            end
        else
            Ring{G,T,S,N,M}(a.v,Values(a.c[1:j-1]...,c,a.c[j+1:end]...))
        end
    end
end

function Base.:+(a::Group{G,T,S,N},b::Ring{G,T,S,N,M}) where {G,T,S,N,M}
    j = findfirst(z->z==a.v,b.v)
    if isnothing(j)
        Ring{G,T,S,N,M+1}(Values((a.v,b.v...)),Values(a.c,b.c...))
    else
        c = a.c+b.c[j]
        if iszero(c)
            if iszero(M-1)
                zero(Ring{G,T,S,N})
            else
                Ring{G,T,S,N,M-1}(Values((b.v[1:j-1]...,b.v[j+1:end]...)),Values(b.c[1:j-1]...,b.c[j+1:end]...))
            end
        else
            Ring{G,T,S,N,M}(a.v,Values(b.c[1:j-1]...,c,b.c[j+1:end]...))
        end
    end
end
function Base.:-(a::Group{G,T,S,N},b::Ring{G,T,S,N,M}) where {G,T,S,N,M}
    j = findfirst(z->z==a.v,b.v)
    if isnothing(j)
        Ring{G,T,S,N,M+1}(Values((a.v,b.v...)),Values(a.c,-b.c...))
    else
        c = a.c-b.c[j]
        if iszero(c)
            if iszero(M-1)
                zero(Ring{G,T,S,N})
            else
                Ring{G,T,S,N,M-1}(Values((b.v[1:j-1]...,b.v[j+1:end]...)),Values(b.c[1:j-1]...,b.c[j+1:end]...))
            end
        else
            Ring{G,T,S,N,M}(b.v,Values(-b.c[1:j-1]...,c,-b.c[j+1:end]...))
        end
    end
end

function Base.:+(a::Ring{G,T,S,N,M},b::Ring{G,T,S,N,L}) where {G,T,S,N,M,L}
    j = findall(z->z∈a.v,b.v)
    jj = [findfirst(z->z==b.v[i],a.v) for i ∈ j]
    if isempty(j)
        Ring{G,T,S,N,M+L}(Values((a.v...,b.v...)),Values(a.c...,b.c...))
    else
        c = Variables(a.c)
        c[jj] += b.c[j]
        jjj = [i for i ∈ 1:L if i∉j]
        j4 = [i for i ∈ 1:M if !iszero(c[i])]
        l = length(j4)+length(jjj)
        if iszero(l)
            zero(Ring{G,T,S,N})
        else
            Ring{G,T,S,N,l}(Values((a.v[j4]...,b.v[jjj]...)),Values(c[j4]...,b.c[jjj]...))
        end
    end
end
function Base.:-(a::Ring{G,T,S,N,M},b::Ring{G,T,S,N,L}) where {G,T,S,N,M,L}
    j = findall(z->z∈b.v,a.v)
    jj = [findfirst(z->z==b.v[i],a.v) for i ∈ j]
    if isempty(j)
        Ring{G,T,S,N,M+L}(Values((a.v...,b.v...)),Values(a.c...,-b.c...))
    else
        c = Variables(a.c)
        c[jj] -= b.c[j]
        jjj = [i for i ∈ 1:L if i∉j]
        j4 = [i for i ∈ 1:M if !iszero(c[i])]
        l = length(j4)+length(jjj)
        if iszero(l)
            zero(Ring{G,T,S,N})
        else
            Ring{G,T,S,N,l}(Values((a.v[j4]...,b.v[jjj]...)),Values(c[j4]...,-b.c[jjj]...))
        end
    end
end

function Base.:*(a::Ring{G,T,S,N,M},b::Group{G,T,S,N}) where {G,T,S,N,M}
    Ring{G,T,S,N,M}(a.v.+Ref(b.v),a.c.*Ref(b.c))
end
function Base.:*(a::Group{G,T,S,N},b::Ring{G,T,S,N,M}) where {G,T,S,N,M}
    Ring{G,T,S,N,M}(Ref(a.v).+b.v,Ref(a.c).*b.c)
end
function Base.:/(a::Ring{G,T,S,N,M},b::Group{G,T,S,N}) where {G,T,S,N,M}
    Ring{G,T,S,N,M}(a.v.-Ref(b.v),a.c./Ref(b.c))
end

function Base.:*(a::Ring{G,T,S,N,M},b::Ring{G,T,S,N,L}) where {G,T,S,N,M,L}
    s = zero(Ring{G,T,S,N})
    for i ∈ 1:L
        s += a*Group{G,T,S,N}(b.v[i],b.c[i])
    end
    return s
end

Base.show(io::IO,::Ring{G,T,S,N,0}) where {G,T,S,N} = print(io,"𝟎")

function Base.show(io::IO,p::Ring{G,T,S,N,M}) where {G,T,S,N,M}
    show(io,Group{G,T,S,N}(p.v[1],p.c[1]))
    for i ∈ 2:M
        if !iszero(p.c[i])
            print(io," + ")
            show(io,Group{G,T,S,N}(p.v[i],p.c[i]))
        end
    end
end
