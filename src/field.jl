
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

export Composite, Field

struct Composite{G,F,T,S,N} <: AbstractModule
    f::Values{N,F}
    v::Values{N,T}
    c::S
end

struct Field{G,F,T,S,N,M} <: AbstractModule
    f::Values{N,F}
    v::Values{M,Values{N,T}}
    c::Values{M,S}
end

Field(g::Composite{G,F,T,S,N}) where {G,F,T,S,N} = Field{G,F,T,S,N,1}(g.f,Values((g.v,)),Values(g.c))
Field(r::Ring{G,T,S,N}) where {G,T,S,N} = Field{G,Number,T,S,1,1}(Values(r),Values((Values(1),)),Values(1))

@pure Field{G,F,T}(f,v,c=Values(1)) where {G,F,T} = Field{G,F,T,eltype(c),length(v),length(c)}(f,v,c)
@pure Field{G,F,T}(f::Values{N,F},v::Values{M,Values{N,T}},c::Values{M,S}=Values(1)) where {G,F,T,S,N,M} = Field{G,F,T,S,N,M}(f,v,c)
@pure Field(f::Values{N,F},v::Values{M,Values{N,T}},c::Values{M,S}=Values(1)) where {N,F,T,S,M} = Field{N,F,T,S,N,M}(f,v,c)
@pure Field(f,v::Values,c,G) = Field(f,v,c,Val(G))
@pure Field(f::Values{N,F},v::Values{M,Values{N,T}},c::Values{M,S},::Val{G}) where {N,F,T,S,M,G} = Field{G,F,T,S,N,M}(f,v,c)

#=@pure function Field(f::Values{N,F},v::Values{N,<:Rational},c::Values{M,S},::Val{G}) where {N,F,S,M,G}
    r = promoteints(v)
    Field{G,F,eltype(r),S,N,M}(r,c)
end=#

name(g::Field{G}) where G = G
valname(g::Field{G}) where G = Val(G)
dimension(g::Field{G,F,T,S,N} where {G,F,T,S}) where N = N
value(g::Field) = g.v
coef(g::Field) = FieldConstants.measure.(g.c)
Base.length(g::Field{G,F,T,S,N,M} where {G,F,T,S,N}) where M = M

Base.signbit(::Field) = false

Base.zero(::Type{Field{G}}) where G = zero(Field{G,Int,Int,Int})
Base.one(::Type{Field{G}}) where G = one(Field{G,Int,Int,Int})

Base.zero(::Type{Field{G,F,T,S}}) where {G,F,T,S} = Field{G,F,T,S,0,0}(Values{0,F}(),Values{0,Values{0,T}}(),Values{0,S}())
Base.zero(::Field{G,F,T,S}) where {G,F,T,S} = Field{G,F,T,S,N,0}(Values{0,F}(),Values{0,Values{0,T}}(),Values{0,S}())
Base.one(::Type{Field{G,F,T,S}}) where {G,F,T,S} = Field{G,F,T,S,1,1}(Values{1,F}(one(F)),Values{1,Values{1,T}}((zeros(Values{1,T}),)),Values{1,S}(one(S)))
Base.one(::Field{G,F,T,S}) where {G,F,T,S} = Field{G,F,T,S,1,1}(Values{1,F}(one(F)),Values{1,Values{1,T}}((zeros(Values{1,T}),)),Values{1,S}(one(S)))

#(f::Field{G,F,T,S,N,M})(v::Values{N}) where {G,F,T,S,N,M} = sum([prod(v.^f.v[i]) for i ∈ 1:M])
#(f::Field{G,F,T,S,N,M})(args...) where {G,F,T,S,N,M} = f(Values(args...))

Base.inv(a::Field{G,F,T,S,N,1}) where {G,F,T,S,N} = Field{G,F,T,S,N,1}(a.f,-a.v,Values(inv(a.c[1])))
Base.:*(a::Number,b::Field{G}) where G = times(factorize(a,Val(G)),b)
Base.:*(a::Field{G},b::Number) where G = times(a,factorize(b,Val(G)))
Base.:/(a::Number,b::Field) = a*inv(b)#
Base.:/(a::Field{G},b::Number) where G = times(a,inv(factorize(b,Val(G))))#

times(a::Field,b::Field) = a*b
times(a::Number,b::Field{G,F,T}) where {G,F,T} = Field{G,F,T}(b.f,b.v,coefprod.(Ref(a),b.c))
times(a::Field{G,F,T},b::Number) where {G,F,T} = Field{G,F,T}(a.f,a.v,coefprod(a.c,Ref(b)))

Base.:-(f::Field{G,F,T,S,N,M}) where {G,F,T,S,N,M} = Field{G,F,T,S,N,M}(f.f,f.v,-f.c)

function Base.:+(a::Composite{G,F,T,S,N},b::Composite{G,F,T,S,N}) where {G,F,T,S,N}
    if a.f≠b.f
        add(Field{G,F,T,S,N,1}(a.f,Values((a.v,)),Values(a.c)),b.f,b.v,b.c,Val(+))
    elseif a.v≠b.v
        Field{G,F,T,S,N,2}(a.f,Values(a.v,b.v),Values(a.c,b.c))
    else
        Field{G,F,T,S,N,1}(a.f,Values((a.v,)),Values(a.c+b.c))
    end
end
function Base.:-(a::Composite{G,F,T,S,N},b::Composite{G,F,T,S,N}) where {G,F,T,S,N}
    if a.f≠b.f
        add(Field{G,F,T,S,N,1}(a.f,Values((a.v,)),Values(a.c)),b.f,b.v,b.c,Val(-))
    elseif a.v≠b.v
        Field{G,F,T,S,N,2}(a.f,Values(a.v,b.v),Values(a.c,-b.c))
    else
        Field{G,F,T,S,N,1}(a.f,Values((a.v,),Values(a.c-b.c)))
    end
end
function Base.:+(a::Field{G,F,T,S,N,1},b::Field{G,F,T,S,N,1}) where {G,F,T,S,N}
    if a.f≠b.f
        add(a,b.f,b.v[1],b.c[1],Val(+))
    elseif a.v≠b.v
        Field{G,F,T,S,N,2}(a.f,Values(a.v[1],b.v[1]),Values(a.c[1],b.c[1]))
    else
        Field{G,F,T,S,N,1}(a.f,a.v,a.c+b.c)
    end
end
function Base.:-(a::Field{G,F,T,S,N,1},b::Field{G,F,T,S,N,1}) where {G,F,T,S,N}
    if a.f≠b.f
        add(a,b.f,b.v[1],b.c[1],Val(-))
    elseif a.v≠b.v
        Field{G,F,T,S,N,2}(a.f,Values(a.v[1],b.v[1]),Values(a.c[1],-b.c[1]))
    else
        Field{G,F,T,S,N,1}(a.f,a.v,a.c-b.c)
    end
end
Base.:+(a::Field{G,F,T,S,N,0},b::Field{G,F,T,S,N,0}) where {G,F,T,S,N} = a
Base.:-(a::Field{G,F,T,S,N,0},b::Field{G,F,T,S,N,0}) where {G,F,T,S,N} = a

pad(a::Values,::Val{M}) where M = Values(a...,zeros(Values{M,Int})...)
pad(a::Values{N},b::Values{M,T}) where {N,M,T} = (pad.(a,Val(M)),Values(zeros(Values{N,T})...,b...))
pad2(b::Values,::Val{N}) where N = Values(zeros(Values{N,Int})...,b...)
pad2(a::Values{N},b::Values{N2,Values{M,T}}) where {N,N2,M,T} = (pad.(a,Val(M)),pad2.(b,Val(N)))

Base.:+(a::Field{G,F,T,S},b::Composite{G,F,T,S}) where {G,F,T,S} = add(a,b.f,b.v,b.c,Val(+))
Base.:-(a::Field{G,F,T,S},b::Composite{G,F,T,S}) where {G,F,T,S} = add(a,b.f,b.v,b.c,Val(-))
Base.:+(a::Field{G,F,T,S},b::Field{G,F,T,S,N,1}) where {G,F,T,S,N} = add(a,b.f,b.v[1],b.c[1],Val(+))
Base.:-(a::Field{G,F,T,S},b::Field{G,F,T,S,N,1}) where {G,F,T,S,N} = add(a,b.f,b.v[1],b.c[1],Val(-))

Base.:+(a::Composite{G,F,T,S},b::Field{G,F,T,S}) where {G,F,T,S} = add2(a.f,a.v,a.c,b,Val(+))
Base.:-(a::Composite{G,F,T,S},b::Field{G,F,T,S}) where {G,F,T,S} = add2(a.f,a.v,a.c,b,Val(-))
Base.:+(a::Field{G,F,T,S,N,1},b::Field{G,F,T,S}) where {G,F,T,S,N} = add2(a.f,a.v[1],a.c[1],b,Val(+))
Base.:-(a::Field{G,F,T,S,N,1},b::Field{G,F,T,S}) where {G,F,T,S,N} = add2(a.f,a.v[1],a.c[1],b,Val(-))

function ad(::Type{Field{G,F,T,S,N,M}},av,bv,of,ac,bc,::Val{op}) where {G,F,T,S,N,M,op}
    j = findfirst(z->z==bv,av)
    if isnothing(j)
        Field{G,F,T,S,N,M+1}(of,Values((av...,bv)),Values(ac...,op(bc)))
    else
        c = op(ac[j],bc)
        if iszero(c)
            if iszero(M-1)
                zero(Field{G,F,T,S})
            else
                Field{G,F,T,S,N,M-1}(of,Values((av[1:j-1]...,av[j+1:end]...)),Values(ac[1:j-1]...,ac[j+1:end]...))
            end
        else
            Field{G,F,T,S,N,M}(of,av,Values(ac[1:j-1]...,c,ac[j+1:end]...))
        end
    end
end

function ad2(::Type{Field{G,F,T,S,N,M}},av,bv,of,ac,bc,::Val{op}) where {G,F,T,S,N,M,op}
    j = findfirst(z->z==av,bv)
    if isnothing(j)
        Field{G,F,T,S,N,M+1}(of,Values((av,bv...)),Values(ac,op(bc)...))
    else
        c = op(ac,bc[j])
        if iszero(c)
            if iszero(M-1)
                zero(Field{G,F,T,S})
            else
                obc = op(bc)
                Field{G,F,T,S,N,M-1}(of,Values((bv[1:j-1]...,bv[j+1:end]...)),Values(obc[1:j-1]...,obc[j+1:end]...))
            end
        else
            obc = op(bc)
            Field{G,F,T,S,N,M}(of,bv,Values(obc[1:j-1]...,c,obc[j+1:end]...))
        end
    end
end

function ad(::Type{Field{G,F,T,S,N,M}},av,bv,of,ac,bc::Values{L},::Val{+}) where {G,F,T,S,N,M,L}
    j = findall(z->z∈av,bv)
    if isempty(j)
        Field{G,F,T,S,N,M+L}(of,Values((av...,bv...)),Values(ac...,bc...))
    else
        c = Variables(ac)
        jj = [findfirst(z->z==bv[i],av) for i ∈ j]
        c[jj] += bc[j]
        jjj = [i for i ∈ 1:L if i∉j]
        j4 = [i for i ∈ 1:M if !iszero(c[i])]
        l = length(j4)+length(jjj)
        if iszero(l)
            zero(Field{G,F,T,S})
        else
            Field{G,F,T,S,N,l}(of,Values((av[j4]...,bv[jjj]...)),Values(c[j4]...,bc[jjj]...))
        end
    end
end

function ad(::Type{Field{G,F,T,S,N,M}},av,bv,of,ac,bc::Values{L},::Val{-}) where {G,F,T,S,N,M,L}
    j = findall(z->z∈av,bv)
    if isempty(j)
        Field{G,F,T,S,N,M+L}(of,Values((av...,bv...)),Values(ac...,-bc...))
    else
        c = Variables(ac)
        jj = [findfirst(z->z==bv[i],av) for i ∈ j]
        c[jj] -= bc[j]
        jjj = [i for i ∈ 1:L if i∉j]
        j4 = [i for i ∈ 1:M if !iszero(c[i])]
        l = length(j4)+length(jjj)
        if iszero(l)
            zero(Field{G,F,T,S})
        else
            Field{G,F,T,S,N,l}(of,Values((av[j4]...,bv[jjj]...)),Values(c[j4]...,-bc[jjj]...))
        end
    end
end

function stuff(var,in,as,bs)
    out = zeros(var)
    out[as] = in[bs]
    return Values(out)
end

let combine = quote
        lap = length(ap1)
        ap = Values{lap,Int}(ap1...)
        bp1 = [findfirst(z->z==a.f[i],bf) for i ∈ ap]
        lbp = length(bp1)
        bp = Values{lbp,Int}(bp1...)
        be1 = [i for i∈1:N2 if i∉bp]
        lbe = length(be1)
        be = Values{lbe,Int}(be1...)
        ae = countvalues(N1+1,N+lbe)
        as,bs = Values(ap...,ae...),Values(bp...,be...)
        obv1 = Variables{N1+lbe,Int}
    end
    @eval begin
        function add(a::Field{G,F,T,S,N1,M},bf::Values{N2},bv,bc,op) where {G,F,T,S,N1,N2,M}
            ap1 = findall(z->z∈bf,a.f)
            field,oav,obv,of = if isempty(ap1)
                (Field{G,F,T,S,N1+N2,M},pad(a.v,bv)...,Values((a.f...,bf...)))
            else
                $combine
                Field{G,F,T,S,N1+lbe,M},pad.(a.v,Val(lbe)),stuff(obv1,bv,as,bs),Values((a.f...,bf[be]...))
            end
            ad(field,oav,obv,of,a.c,bc,op)
        end
        function add2(a::Field{G,F,T,S,N1,M},bf::Values{N2},bv,bc,op) where {G,F,T,S,N1,N2,M}
            ap1 = findall(z->z∈bf,a.f)
            field,oav,obv,of = if isempty(ap1)
                (Field{G,F,T,S,N1+N2,M},pad(a.v,bv)...,Values((a.f...,bf...)))
            else
                $combine
                Field{G,F,T,S,N1+lbe,M},pad.(a.v,Val(lbe)),stuff(obv1,bv,as,bs),Values((a.f...,bf[be]...))
            end
            ad2(field,oav,obv,of,a.c,bc,op)
        end
        function Base.:+(a::Field{G,F,T,S,N1,M},b::Field{G,F,T,S,N2,L}) where {G,F,T,S,N1,N2,M,L}
            ap1 = findall(z->z∈b.f,a.f)
            field,oav,obv,of = if isempty(ap1)
                (Field{G,F,T,S,N1+N2,M},pad(a.v,b.v)...,Values((a.f...,b.f...)))
            else
                bf = b.f
                $combine
                Field{G,F,T,S,N1+lbe,M},pad.(a.v,Val(lbe)),stuff.(obv1,b.v,Ref(as),Ref(bs)),Values((a.f...,b.f[be]...))
            end
            ad(field,oav,obv,of,a.c,b.c,Val(+))
        end
        function Base.:-(a::Field{G,F,T,S,N1,M},b::Field{G,F,T,S,N2,L}) where {G,F,T,S,N1,N2,M,L}
            ap1 = findall(z->z∈b.f,a.f)
            field,oav,obv,of = if isempty(ap1)
                (Field{G,F,T,S,N1+N2,M},pad(a.v,b.v)...,Values((a.f...,b.f...)))
            else
                bf = b.f
                $combine
                Field{G,F,T,S,N1+lbe,M},pad.(a.v,Val(lbe)),stuff.(obv1,b.v,Ref(as),Ref(bs)),Values((a.f...,b.f[be]...))
            end
            ad(field,oav,obv,of,a.c,b.c,Val(-))
        end
        function Base.:*(a::Field{G,F,T,S,N1,1},b::Field{G,F,T,S,N2,1}) where {G,F,T,S,N1,N2}
            ap1 = findall(z->z∈b.f,a.f)
            field,oav,obv,of = if isempty(ap1)
                (Field{G,F,T,S,N1+N2,1},pad2(a.v,b.v)...,Values((a.f...,b.f...)))
            else
                bf = b.f
                $combine
                Field{G,F,T,S,N1+lbe,1},pad.(a.v,Val(lbe)),stuff.(obv1,b.v,Ref(as),Ref(bs)),Values((a.f...,b.f[be]...))
            end
            field(of,oav+obv,a.c.*Ref(b.c[1]))
        end
        function Base.:/(a::Field{G,F,T,S,N1,1},b::Field{G,F,T,S,N2,1}) where {G,F,T,S,N1,N2}
            ap1 = findall(z->z∈b.f,a.f)
            field,oav,obv,of = if isempty(ap1)
                (Field{G,F,T,S,N1+N2,1},pad2(a.v,b.v)...,Values((a.f...,b.f...)))
            else
                bf = b.f
                $combine
                Field{G,F,T,S,N1+lbe,1},pad.(a.v,Val(lbe)),stuff.(obv1,b.v,Ref(as),Ref(bs)),Values((a.f...,b.f[be]...))
            end
            field(of,oav-obv,a.c./Ref(b.c[1]))
        end
        function Base.:*(a::Field{G,F,T,S,N1,M},b::Composite{G,F,T,S,N2}) where {G,F,T,S,N1,N2,M}
            ap1 = findall(z->z∈b.f,a.f)
            field,oav,obv,of = if isempty(ap1)
                (Field{G,F,T,S,N1+N2,M},pad(a.v,b.v)...,Values((a.f...,b.f...)))
            else
                bf = b.f
                $combine
                Field{G,F,T,S,N1+lbe,M},pad.(a.v,Val(lbe)),stuff(obv1,b.v,as,bs),Values((a.f...,b.f[be]...))
            end
            field(of,oav.+Ref(obv),a.c.*Ref(b.c))
        end
        Base.:*(a::Composite{G,F,T,S,N1},b::Field{G,F,T,S,N2,M}) where {G,F,T,S,N1,N2,M} = Field(a)*b
        function Base.:/(a::Field{G,F,T,S,N1,M},b::Composite{G,F,T,S,N2}) where {G,F,T,S,N1,N2,M}
            ap1 = findall(z->z∈b.f,a.f)
            field,oav,obv,of = if isempty(ap1)
                (Field{G,F,T,S,N1+N2,M},pad(a.v,b.v)...,Values((a.f...,b.f...)))
            else
                bf = b.f
                $combine
                Field{G,F,T,S,N1+lbe,M},pad.(a.v,Val(lbe)),stuff(obv1,b.v,as,bs),Values((a.f...,b.f[be]...))
            end
            field(oav.-Ref(obv),a.c./Ref(b.c))
        end
        Base.:/(a::Composite{G,F,T,S,N1},b::Field{G,F,T,S,N2,M}) where {G,F,T,S,N1,N2,M} = Field(a)*b
        function Base.:*(a::Field{G,F,T,S,N1,M},b::Field{G,F,T,S,N2,L}) where {G,F,T,S,N1,N2,M,L}
            ap1 = findall(z->z∈b.f,a.f)
            field,oav,obv,of = if isempty(ap1)
                (Composite{G,F,T,S,N1+N2},pad2(a.v,b.v)...,Values((a.f...,b.f...)))
            else
                bf = b.f
                $combine
                Composite{G,F,T,S,N1+lbe},pad.(a.v,Val(lbe)),stuff.(obv1,b.v,Ref(as),Ref(bs)),Values((a.f...,b.f[be]...))
            end
            s = zero(Field{G,F,T,S})
            for i ∈ 1:L
                s += a*field(of,b.v[i],b.c[i])
            end
            return s
        end
    end
end

Base.show(io::IO,::Field{G,F,T,S,N,0}) where {G,F,T,S,N} = print(io,"𝟎")

function Base.show(io::IO,p::Field{G,F,T,S,N,M}) where {G,F,T,S,N,M}
    show(io,Composite{G,F,T,S,N}(p.f,p.v[1],p.c[1]))
    for i ∈ 2:M
        if !iszero(p.c[i])
            print(io," + ")
            show(io,Composite{G,F,T,S,N}(p.f,p.v[i],p.c[i]))
        end
    end
end
