
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

@pure Ring{G,T}(v,c=Values(1)) where {G,T} = Ring{G,T,eltype(c),length(v),length(c)}(v,c)
@pure Ring{G,T}(v::Values{M,Values{N,T}},c::Values{M,S}=Values(1)) where {G,T,S,N,M} = Ring{G,T,S,N,M}(v,c)
@pure Ring(v::Values{M,Values{N,T}},c::Values{M,S}=Values(1)) where {N,T,S,M} = Ring{N,T,S,N,M}(v,c)
@pure Ring(v::Values,c,G) = Ring(v,c,Val(G))
@pure Ring(v::Values{M,Values{N,T}},c::Values{M,S},::Val{G}) where {N,T,S,M,G} = Ring{G,T,S,N,M}(v,c)

#=@pure function Ring(v::Values{N,<:Rational},c::Values{M,S},::Val{G}) where {N,S,M,G}
    r = promoteints(v)
    Ring{G,eltype(r),S,N,M}(r,c)
end=#

name(g::Ring{G}) where G = G
valname(g::Ring{G}) where G = Val(G)
dimension(g::Ring{G,T,S,N} where {G,T,S}) where N = N
value(g::Ring) = g.v
coef(g::Ring) = FieldConstants.measure.(g.c)
Base.length(g::Ring{G,T,S,N,M} where {G,T,S,N}) where M = M

Base.signbit(::Ring) = false

Base.zero(::Type{Ring{G,T,S,N}}) where {G,T,S,N} = Ring{G,T,S,N,0}(Values{0,Values{N,T}}(),Values{0,S}())
Base.zero(::Ring{G,T,S,N}) where {G,T,S,N} = Ring{G,T,S,N,0}(Values{0,Values{N,T}}(),Values{0,S}())
Base.one(::Type{Ring{G,T,S,N}}) where {G,T,S,N} = Ring{G,T,S,N,1}(Values{1,Values{N,T}}((zeros(Values{N,T}),)),Values{1,S}(1))
Base.one(::Ring{G,T,S,N}) where {G,T,S,N} = Ring{G,T,S,N,1}(Values{1,Values{N,T}}((zeros(Values{N,T}),)),Values{1,S}(1))

(f::Ring{G,T,S,N,M})(v::Values{N}) where {G,T,S,N,M} = sum([prod(v.^f.v[i]) for i ∈ 1:M])
(f::Ring{G,T,S,N,M})(args...) where {G,T,S,N,M} = f(Values(args...))

Base.inv(a::Ring{G,T,S,N,1}) where {G,T,S,N} = Ring{G,T,S,N,1}(-a.v,Values(inv(a.c[1])))
Base.:*(a::Number,b::Ring{G}) where G = times(factorize(a,Val(G)),b)
Base.:*(a::Ring{G},b::Number) where G = times(a,factorize(b,Val(G)))
Base.:/(a::Number,b::Ring) = a*inv(b)#
Base.:/(a::Ring{G},b::Number) where G = times(a,inv(factorize(b,Val(G))))#

times(a::Ring,b::Ring) = a*b
times(a::Number,b::Ring{G,T}) where {G,T} = Ring{G,T}(b.v,coefprod.(Ref(a),b.c))
times(a::Ring{G,T},b::Number) where {G,T} = Ring{G,T}(a.v,coefprod(a.c,Ref(b)))

Base.:-(f::Ring{G,T,S,N,M}) where {G,T,S,N,M} = Ring{G,T,S,N,M}(f.v,-f.c)

function Base.:+(a::Group{G,T,S,N},b::Group{G,T,S,N}) where {G,T,S,N}
    if a.v≠b.v
        Ring{G,T,S,N,2}(Values(a.v,b.v),Values(a.c,b.c))
    else
        Ring{G,T,S,N,1}(Values((a.v,)),Values(a.c+b.c))
    end
end
function Base.:-(a::Group{G,T,S,N},b::Group{G,T,S,N}) where {G,T,S,N}
    if a.v≠b.v
        Ring{G,T,S,N,2}(Values(a.v,b.v),Values(a.c,-b.c))
    else
        Ring{G,T,S,N,1}(Values((a.v,),Values(a.c-b.c)))
    end
end
function Base.:+(a::Ring{G,T,S,N,1},b::Ring{G,T,S,N,1}) where {G,T,S,N}
    if a.v≠b.v
        Ring{G,T,S,N,2}(Values(a.v[1],b.v[1]),Values(a.c[1],b.c[1]))
    else
        Ring{G,T,S,N,1}(a.v,a.c+b.c)
    end
end
function Base.:-(a::Ring{G,T,S,N,1},b::Ring{G,T,S,N,1}) where {G,T,S,N}
    if a.v≠b.v
        Ring{G,T,S,N,2}(Values(a.v[1],b.v[1]),Values(a.c[1],-b.c[1]))
    else
        Ring{G,T,S,N,1}(a.v,a.c-b.c)
    end
end
Base.:+(a::Ring{G,T,S,N,0},b::Ring{G,T,S,N,0}) where {G,T,S,N} = a
Base.:-(a::Ring{G,T,S,N,0},b::Ring{G,T,S,N,0}) where {G,T,S,N} = a

function add(a::Ring{G,T,S,N,M},bv,bc,::Val{op}) where {G,T,S,N,M,op}
    j = findfirst(z->z==bv,a.v)
    if isnothing(j)
        Ring{G,T,S,N,M+1}(Values((a.v...,bv)),Values(a.c...,op(bc)))
    else
        c = op(a.c[j],bc)
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

Base.:+(a::Ring{G,T,S,N,M},b::Group{G,T,S,N}) where {G,T,S,N,M} = add(a,b.v,b.c,Val(+))
Base.:-(a::Ring{G,T,S,N,M},b::Group{G,T,S,N}) where {G,T,S,N,M} = add(a,b.v,b.c,Val(-))
Base.:+(a::Ring{G,T,S,N,M},b::Ring{G,T,S,N,1}) where {G,T,S,N,M} = add(a,b.v[1],b.c[1],Val(+))
Base.:-(a::Ring{G,T,S,N,M},b::Ring{G,T,S,N,1}) where {G,T,S,N,M} = add(a,b.v[1],b.c[1],Val(-))

function add2(av,ac,b::Ring{G,T,S,N,M},::Val{op}) where {G,T,S,N,M,op}
    j = findfirst(z->z==av,b.v)
    if isnothing(j)
        Ring{G,T,S,N,M+1}(Values((av,b.v...)),Values(ac,op(b.c)...))
    else
        c = op(ac,b.c[j])
        if iszero(c)
            if iszero(M-1)
                zero(Ring{G,T,S,N})
            else
                bc = op(b.c)
                Ring{G,T,S,N,M-1}(Values((b.v[1:j-1]...,b.v[j+1:end]...)),Values(bc[1:j-1]...,bc[j+1:end]...))
            end
        else
            bc = op(b.c)
            Ring{G,T,S,N,M}(b.v,Values(bc[1:j-1]...,c,bc[j+1:end]...))
        end
    end
end

Base.:+(a::Group{G,T,S,N},b::Ring{G,T,S,N,M}) where {G,T,S,N,M} = add2(a.v,a.c,b,Val(+))
Base.:-(a::Group{G,T,S,N},b::Ring{G,T,S,N,M}) where {G,T,S,N,M} = add2(a.v,a.c,b,Val(-))
Base.:+(a::Ring{G,T,S,N,1},b::Ring{G,T,S,N,M}) where {G,T,S,N,M} = add2(a.v[1],a.c[1],b,Val(+))
Base.:-(a::Ring{G,T,S,N,1},b::Ring{G,T,S,N,M}) where {G,T,S,N,M} = add2(a.v[1],a.c[1],b,Val(-))

function Base.:+(a::Ring{G,T,S,N,M},b::Ring{G,T,S,N,L}) where {G,T,S,N,M,L}
    j = findall(z->z∈a.v,b.v)
    if isempty(j)
        Ring{G,T,S,N,M+L}(Values((a.v...,b.v...)),Values(a.c...,b.c...))
    else
        c = Variables(a.c)
        jj = [findfirst(z->z==b.v[i],a.v) for i ∈ j]
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
    j = findall(z->z∈a.v,b.v)
    if isempty(j)
        Ring{G,T,S,N,M+L}(Values((a.v...,b.v...)),Values(a.c...,-b.c...))
    else
        c = Variables(a.c)
        jj = [findfirst(z->z==b.v[i],a.v) for i ∈ j]
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

function Base.:*(a::Ring{G,T,S,N,1},b::Ring{G,T,S,N,1}) where {G,T,S,N}
    Ring{G,T,S,N,1}(a.v+b.v,a.c.*Ref(b.c[1]))
end
function Base.:/(a::Ring{G,T,S,N,1},b::Ring{G,T,S,N,1}) where {G,T,S,N}
    Ring{G,T,S,N,1}(a.v-b.v,a.c./Ref(b.c[1]))
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
