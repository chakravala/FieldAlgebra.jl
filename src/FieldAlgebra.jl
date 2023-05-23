module FieldAlgebra

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
#
#  _____ _      _     _    _    _            _
# |  ___(_) ___| | __| |  / \  | | __ _  ___| |__  _ __ __ _
# | |_  | |/ _ \ |/ _` | / _ \ | |/ _` |/ _ \ '_ \| '__/ _` |
# |  _| | |  __/ | (_| |/ ___ \| | (_| |  __/ |_) | | | (_| |
# |_|   |_|\___|_|\__,_/_/   \_\_|\__, |\___|_.__/|_|  \__,_|
#                                 |___/

import Base: @pure
import FieldConstants
import AbstractTensors: TupleVector, Values, value, Variables
using LinearAlgebra

import FieldConstants: isconstant, Constant, measure, logdb, expdb, dB

export AbstractModule, AbelianGroup, Group, LogGroup, ExpGroup
export value, isonezero, islog, isexp, base, dimensions

const alphabet = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
@pure letters(N) = Values{N,Char}([alphabet[i] for i ∈ 1:N])

abstract type AbstractModule <: Number end

abstract type AbelianGroup <: AbstractModule end

isgroup(::AbelianGroup) = true
isgroup(::Constant{G}) where G = isgroup(G)
isgroup(x) = false

struct Group{G,T,S,N} <: AbelianGroup
    v::Values{N,T}
    c::S
    @pure function Group{G,T,S,N}(v,c) where {G,T,S,N}
        r = promoteint(FieldConstants.cache(c))
        new{G,T,typeof(r),N}(v,r)
    end
    @pure function Group{G,T,S,N}(v,c) where {G,T<:Rational,S,N}
        r,p = promoteints(v),promoteint(FieldConstants.cache(c))
        new{G,eltype(r),typeof(p),N}(r,p)
    end
    @pure function Group{G,T,S,N}(v::Values{T,N},c) where {G,T<:Rational,S,N}
        r,p = promoteints(v),promoteint(FieldConstants.cache(c))
        new{G,eltype(r),typeof(p),N}(r,p)
    end
end

@pure Group{G,T}(v,c::S=1) where {G,T,S} = Group{G,T,S,length(v)}(v,c)
@pure Group{G,T}(v::Values{N,T},c::S=1) where {G,T,S,N} = Group{G,T,S,N}(v,c)
@pure Group(v::Values{N,T},c::S=1) where {N,T,S} = Group{N,T,S,N}(v,c)
@pure Group(v::Values,c,G) = Group(v,c,Val(G))
@pure Group(v::Values{N,T},c::S,::Val{G}) where {N,T,S,G} = Group{G,T,S,N}(v,c)

@pure function Group(v::Values{N,<:Rational},c::S,::Val{G}) where {N,S,G}
    r = promoteints(v)
    Group{G,eltype(r),S,N}(r,c)
end

name(g::Group{G}) where G = G
valname(g::Group{G}) where G = Val(G)
dimension(g::Group{G,T,S,N} where {G,T,S}) where N = N
value(g::Group) = g.v
coef(g::Group) = FieldConstants.measure(g.c)

Base.:(==)(a::Group,b::Group) = a.v == b.v && a.c == b.c

Base.abs(a::Group{G,T,S,N}) where {G,T,S,N} = Group{G,T,S,N}(a.v,abs(measure(a.c)))
Base.signbit(g::Group) = signbit(g.c)

@pure isonezero(x) = isone(x) || iszero(x)
@pure checkint(v::T) where T<:Integer = v
@pure checkint(v::T) where T<:Rational = isone(denominator(v))
@pure checkint(v) = isonezero(v)
@pure checkints(v::Values{N} where N) = prod(isonezero.(v.v))
@pure checkints(v::Values{N,<:Rational} where N) = prod(isone.(denominator.(v.v)))
@pure checkints(v::Values{N,<:Integer} where N) = v
@pure promoteint(v::Group) = iszero(prod(v.v)) && !isone(v.c) ? promoteint(v.c) : v
@pure promoteint(v::T) where T<:Integer = v
@pure promoteint(v) = checkint(v) ? Int(v) : v
@pure promoteint(v::FieldConstants.Constant) = isone(v) ? 1 : v
@pure promoteints(v::Values{N,<:Integer} where N) = v
@pure promoteints(v) = checkints(v) ? Int.(v) : v

const expos = Values('⁰','¹','²','³','⁴','⁵','⁶','⁷','⁸','⁹')
const chars = Dict([[string(i-1)[1]=>expos[i] for i ∈ 1:length(expos)];['.'=>'⋅','-'=>'⁻','e'=>'ᵉ','v'=>'ᵛ','₀'=>'⁰','₁'=>'¹','₂'=>'²','₃'=>'³','₄'=>'⁴','₅'=>'⁵','₆'=>'⁶','₇'=>'⁷','₈'=>'⁸','₉'=>'⁹','*'=>'*','⋅'=>'⋅']])

makeint(x) = x
@pure makint(x::Int) = x
@pure function makeint(x::AbstractFloat)
    iszero(x) && return(0)
    ax,rem,ne = abs(x),abs(x%1),sqrt(eps()*norm(x))
    if ne < 1
        if log10(ax)-log(1.7,rem) > 20
            return Int(x÷1)
        elseif log10(ax)-log10(1-rem) > 17
            return Int(x÷1)+1
        else
            return x
        end
    else
        return x
    end
end

findpower(x) = 0
findpower(x::Int,i=Int(round(log10(x),RoundDown))) = i<0 ? 0 : (d = (x÷(10^i))%10; !iszero(d) ? findpower(x,i-1) : i+1)

latexpo(io::IO, d, x) = !iszero(x) && (print(io, d); latexpo(io,x))
function latexpo(io::IO, d, x::AbstractFloat)
    if !iszero(x)
        ix = makeint(x)
        if abs(x) < 1
            mix = makeint(inv(x))
            if typeof(mix) == Int
                latexpo(io, d, 1//mix)
            else
                if (d == 10 || d == "10") && length(string(abs(x)))>5
                    x < 0 && print(io, '/')
                    print(io, makeint(10^abs(x)))
                    !(x<0) && print(io, "\\cdot ")
                else
                    print(io, d)
                    printexpo(io, x)
                end
            end
        elseif d == 10 || d == "10"
            mx = makeint(abs(x))
            x < 0 && print(io, '/')
            if typeof(mx)== Int
                latexpo(io, d, mx)
            else
                ten = makeint(10^abs(x))
                pow = findpower(ten)
                if !iszero(pow)
                    net = ten÷10^pow
                    if !isone(net)
                        print(io, net)
                        print(io, x < 0 ? '/' : '⋅')
                    end
                    print(io, d)
                    latexpo(io, pow)
                elseif length(string(abs(x)))>5
                    print(io, ten)
                    !(x<0) && print(io, '⋅')
                else
                    latexpo(io, d, rationalize(x))
                end
                if !iszero(pow)
                    
                end
            end
        elseif typeof(ix) == Int
            latexpo(io,d,ix)
        else
            print(io, d)
            latexpo(io,x)
        end
    end
end

latexpo(io::IO, x::Integer) = !isone(x) && print(io, "^{", x, '}')

function latexpo(io::IO, x::AbstractFloat)
    if !isone(x)
        print(io,"^{", x, '}')
    end
end

function latexpo(io::IO, x::Rational)
    if !isone(x)
        print(io, "^{", x.num)
        !isone(x.den) && print(io, '/', x.den)
        print(io, '}')
    end
end

function latexpo(io::IO, x::Complex)
    if !isone(x)
        print(io, "^{")
        if !iszero(x.re)
            isone(x.re) ? print(io, '1') : latexpo(io, x.re)
            !iszero(x.im) && print(io, x.im<0 ? '-' : '+')
        else
            x.im<0 && print(io, '-')
        end
        if !iszero(x.im)
            latexpo(io, abs(x.im))
            print(io, "im")
        end
        print(io, '}')
    end
end

function latexnum(io, b, e)
    me = makeint(e)
    !(me<0) && latexpo(io, b, me)
end

function latexdims(io::IO,x::Group{G,T,S,N} where {G,S},name,c="\\cdot ") where {T,N}
    M = 0
    if haskey(ENV,"GROUPAREN")
        for i ∈ 1:N-M
            printnum(io, name[i], x.v[i])
        end
        n = sum(first(x.v,N-M).<0)
        n>0 && print(io, '/')
        n>1 && print(io, '(')
        for i ∈ 1:N-M
            printnum(io, name[i], -x.v[i])
            typeof(name[i])==String && isone(x.v[i]) && !iszero(norm(last(first(x.v,N-M),N-i-1))) && print(io,c)
        end
        n>1 && print(io, ')')
    else
        for i ∈ 1:N-M
            latexpo(io, name[i], makeint(x.v[i]))
            typeof(name[i])==String && isone(x.v[i]) && !iszero(norm(last(first(x.v,N-M),N-i-M))) && print(io,c)
        end
    end
end

special_print(io, x) = print(io, x)
function special_print(io,f::Float64)
    sf = string(f)
    if 'e' ∈ sf
        m = match(r"(\d+.\d+)[e](-?\d+)",sf).captures
        print(io,"$(m[1]) \\times 10^{$(m[2])}")
    else
        print(io, sf)
    end
end

latext(x) = basistext(x)
showlatex(::Constant{x}) where x = showlatex(x)
function showlatex(x::Group)
    io = IOBuffer()
    latexgroup(io,x)
    String(take!(io))
end
function showlatex(D,U)
    io = IOBuffer()
    latexgroup(io,U(D),U)
    String(take!(io))
end
function latexgroup_pre(io::IO,x,u,c="\\mathbb{1}",d="\\cdot ")
    print(io,x)
end
function latexgroup_pre(io::IO,x::Group{G,T,S,N} where {G,S},u=latext(x),c="\\mathbb{1}",d="\\cdot ") where {T,N}
    #back = T<:AbstractFloat && x.v[N]<0
    #!back && printexpo(io, 10, x.v[N])
    latexdims(io,x,u,c isa Char ? d : u[end]≠"" ? d : "\\cdot ")
    iz = iszero(norm(x.v))
    xc = coef(x)
    iz && (isone(xc)||abs(measure(xc))<1) && print(io, c)
    #back && printexpo(io, 10, last(x.v))
    if !isone(xc)
        if float(abs(measure(xc)))<1 && !isgroup(xc)
            print(io, '/')
            special_print(io, makeint(inv(xc)))
        else
            !iz && !(c isa Char) && print(io, "\\cdot ")
            if isgroup(xc)
                print(io, '(')
                latexgroup_pre(io,xc,latext(xc),c,d)
                #special_print(io, float(xc))
                print(io, ')')
            else
                special_print(io, makeint(xc))
            end
        end
    end
end
function latexgroup(io::IO,x::Group{G,T,S,N} where {G,S},u=latext(x),c="\\mathbb{1}") where {T,N}
    latexgroup_pre(io,x,u,c)
    if hasproduct(x)
        print(io, " = ")
        special_print(io, product(x))
    end
end

function latexgroup(io::IO, x::AbelianGroup, u=latext(value(x)), c="\\mathbb{1}")
    showfun(io,x)
    latexgroup_pre(io,value(x),u,c)
    print(io,')')
    if hasproduct(x)
        print(io, " = ")
        special_print(io, product(x))
    end
end


printexpo(io::IO, d, x) = !iszero(x) && (print(io, d); printexpo(io,x))
function printexpo(io::IO, d, x::AbstractFloat)
    if !iszero(x)
        ix = makeint(x)
        if abs(x) < 1
            mix = makeint(inv(x))
            if typeof(mix) == Int
                printexpo(io, d, 1//mix)
            else
                if (d == 10 || d == "10") && length(string(abs(x)))>5
                    x < 0 && print(io, '/')
                    print(io, makeint(10^abs(x)))
                    !(x<0) && print(io, '⋅')
                else
                    print(io, d)
                    printexpo(io, x)
                end
            end
        elseif d == 10 || d == "10"
            mx = makeint(abs(x))
            x < 0 && print(io, '/')
            if typeof(mx)== Int
                printexpo(io, d, mx)
            else
                ten = makeint(10^abs(x))
                pow = findpower(ten)
                if !iszero(pow)
                    net = ten÷10^pow
                    if !isone(net)
                        print(io, net)
                        print(io, x < 0 ? '/' : '⋅')
                    end
                    print(io, d)
                    printexpo(io, pow)
                elseif length(string(abs(x)))>5
                    print(io, ten)
                    !(x<0) && print(io, '⋅')
                else
                    printexpo(io, d, rationalize(x))
                end
                if !iszero(pow)
                    
                end
            end
        elseif typeof(ix) == Int
            printexpo(io,d,ix)
        else
            print(io, d)
            printexpo(io,x)
        end
    end
end

function printexpo(io::IO, x::Integer)
    if !isone(x)
        print(io, (x<0 ? ('⁻',) : ())..., expos[reverse(digits(abs(x)).+1)]...)
    end
end

function printexpo(io::IO, x::AbstractFloat)
    if !isone(x)
        print(io, (x<0 ? ('⁻',) : ())..., [chars[i] for i ∈ string(abs(x))]...)
    end
end

function printexpo(io::IO, x::Rational)
    if !isone(x)
        print(io, (x.num<0 ? ('⁻',) : ())..., expos[reverse(digits(abs(x.num)).+1)]...)
        !isone(x.den) && print(io, 'ᐟ', expos[reverse(digits(x.den).+1)]...)
    end
end

function printexpo(io::IO, x::Complex)
    if !isone(x)
        if !iszero(x.re)
            isone(x.re) ? print(io, '¹') : printexpo(io, x.re)
            !iszero(x.im) && print(io, x.im<0 ? '⁻' : '⁺')
        else
            x.im<0 && print(io, '⁻')
        end
        if !iszero(x.im)
            printexpo(io, abs(x.im))
            print(io, "ⁱᵐ")
        end
    end
end

function printdims(io::IO,x::Group{G,T,S,N} where {G,S},name) where {T,N}
    M = 0
    if haskey(ENV,"GROUPAREN")
        for i ∈ 1:N-M
            printnum(io, name[i], x.v[i])
        end
        n = sum(first(x.v,N-M).<0)
        n>0 && print(io, '/')
        n>1 && print(io, '(')
        for i ∈ 1:N-M
            printnum(io, name[i], -x.v[i])
            typeof(name[i])==String && isone(x.v[i]) && !iszero(norm(last(first(x.v,N-M),N-i-1))) && print(io,'*')
        end
        n>1 && print(io, ')')
    else
        for i ∈ 1:N-M
            printexpo(io, name[i], makeint(x.v[i]))
            typeof(name[i])==String && isone(x.v[i]) && !iszero(norm(last(first(x.v,N-M),N-i-M))) && print(io,'⋅')
        end
    end
end

function printnum(io, b, e)
    me = makeint(e)
    !(me<0) && printexpo(io, b, me)
end

print_special(io,x) = print(io,x)
function print_special(io,f::Float64)
    sf = string(f)
    if 'e' ∈ sf
        m = match(r"(\d+.\d+)[e](-?\d+)",sf).captures
        print(io,"$(m[1])×10")
        printexpo(io,Meta.parse(m[2]))
    else
        print(io, sf)
    end
end

Base.show(io::IO,x::Group) = showgroup(io,x)
function showgroup_pre(io::IO,x::Group{G,T,S,N} where {G,S},u=basistext(x),c='𝟙') where {T,N}
    #back = T<:AbstractFloat && x.v[N]<0
    #!back && printexpo(io, 10, x.v[N])
    printdims(io,x,u)
    iz = iszero(norm(x.v))
    xc = coef(x)
    iz && (isone(xc)||abs(measure(xc))<1) && print(io, c)
    #back && printexpo(io, 10, last(x.v))
    if !isone(xc)
        if float(abs(measure(xc)))<1 && !isgroup(xc)
            print(io,'/',makeint(inv(xc)))
        else
            !iz && print(io, '⋅')
            if isgroup(xc)
                print(io, '(', makeint(xc), ')')
            else
                print(io, makeint(xc))
            end
        end
    end
end
function showgroup(io::IO,x::Group{G,T,S,N} where {G,S},u=basistext(x),c='𝟙') where {T,N}
    showgroup_pre(io,x,u,c)
    if hasproduct(x)
        print(io, " = ", product(x))
        #print_special(io, product(x))
    end
end

function showgroup(io::IO, x::AbelianGroup, u=basistext(value(x)), c='𝟙')
    showfun(io,x)
    showgroup_pre(io,value(x),u,c)
    print(io,')')
    if hasproduct(x)
        print(io, " = ", product(x))
        #print_special(io, product(x))
    end
end

# log

struct LogGroup{B,T<:AbelianGroup} <: AbelianGroup
    v::T
    @pure LogGroup{B,T}(v) where {B,T} = new{B,T}(v)
end

@pure LogGroup{B}(v::T) where {B,T} = LogGroup{B,T}(v)
@pure LogGroup(d::AbelianGroup) = LogGroup{ℯ}(d)

@pure islog(::LogGroup) = true
@pure islog(x) = false

@pure base(x::LogGroup{B}) where B = B
@pure dimension(x::LogGroup) = dimension(value(x))

value(g::LogGroup) = g.v

Base.show(io::IO, x::LogGroup) = showgroup(io,x)

showfun(io::IO, x::LogGroup{B}) where B = print(io,"log(",B,',')
showfun(io::IO, x::LogGroup{ℯ}) = print(io,"log(")
showfun(io::IO, x::LogGroup{2}) = print(io,"log2(")
showfun(io::IO, x::LogGroup{10}) = print(io,"log10(")
showfun(io::IO, x::LogGroup{exp10(0.1)}) = print(io,"dB(")

product(x::LogGroup{B}) where B = log(B,product(value(x)))
product(x::LogGroup{ℯ}) = log(product(value(x)))
product(x::LogGroup{2}) = log2(product(value(x)))
product(x::LogGroup{10}) = log10(product(value(x)))
product(x::LogGroup{exp10(0.1)}) = dB(product(value(x)))

Base.log(x::AbelianGroup) = LogGroup(x)
Base.log2(x::AbelianGroup) = LogGroup{2}(x)
Base.log10(x::AbelianGroup) = LogGroup{10}(x)
Base.log(b::Number,x::AbelianGroup) = LogGroup{b}(x)
Base.exp(x::LogGroup{ℯ}) = value(x)
Base.exp2(x::LogGroup{2}) = value(x)
Base.exp10(x::LogGroup{10}) = value(x)
Base.exp(x::LogGroup{B}) where B = value(x)^inv(log(B))
Base.exp2(x::LogGroup) = exp2(x)
Base.exp10(x::LogGroup) = exp10(x)
Base.:^(b::T,x::LogGroup) where T<:Number = exp(x*log(b))

Base.:+(x::LogGroup{B},y::LogGroup{B}) where B = LogGroup{B}(x.v*y.v)
Base.:-(x::LogGroup{B},y::LogGroup{B}) where B = LogGroup{B}(x.v/y.v)
Base.:/(x::LogGroup{B},y::T) where {B,T<:Number} = LogGroup{B^y}(x.v)
Base.:*(x::LogGroup,y::T) where T<:Number = x/inv(y)
Base.:*(x::T,y::LogGroup) where T<:Number = y*x

# exp

struct ExpGroup{B,T<:AbelianGroup} <: AbelianGroup
    v::T
end

@pure ExpGroup{B}(v::T) where {B,T} = ExpGroup{B,T}(v)
@pure ExpGroup(d::AbelianGroup) = ExpGroup{ℯ}(d)

@pure base(x::ExpGroup{B}) where B = B
@pure dimension(x::ExpGroup) = dimension(value(x))

value(g::ExpGroup) = g.v

Base.show(io::IO, x::ExpGroup) = showgroup(io,x)

showfun(io::IO, x::ExpGroup{B}) where B = print(io,B,"^(")
showfun(io::IO, x::ExpGroup{ℯ}) = print(io,"exp(")
showfun(io::IO, x::ExpGroup{2}) = print(io,"exp2(")
showfun(io::IO, x::ExpGroup{10}) = print(io,"exp10(")

product(x::ExpGroup{B}) where B = B^product(value(x))
product(x::ExpGroup{ℯ}) = exp(product(value(x)))
product(x::ExpGroup{2}) = exp2(product(value(x)))
product(x::ExpGroup{10}) = exp10(product(value(x)))

Base.exp(x::AbelianGroup) = ExpGroup(x)
Base.exp2(x::AbelianGroup) = ExpGroup{2}(x)
Base.exp10(x::AbelianGroup) = ExpGroup{10}(x)
Base.:^(b::T,x::AbelianGroup) where T<:Number = ExpGroup{b}(x)
Base.log(x::ExpGroup{ℯ}) = value(x)
Base.log2(x::ExpGroup{2}) = value(x)
Base.log10(x::ExpGroup{10}) = value(x)
Base.log(b::Number,x::ExpGroup{B}) where B = value(x)/log(B,b)
Base.log(x::ExpGroup) = log(ℯ,x)
Base.log2(x::ExpGroup) = log(2,x)
Base.log10(x::ExpGroup) = log(10,x)

Base.:^(x::ExpGroup{B},y::T) where {B,T<:Number} = iszero(y) ? one(x) : x
Base.:^(x::ExpGroup{B},y::T) where {B,T<:Integer} = iszero(y) ? one(x) : x
Base.:^(x::ExpGroup,y::ExpGroup) = ExpGroup{x}(y)
Base.:*(x::ExpGroup{B},y::ExpGroup{B}) where B = ExpGroup{B}(x.v+y.v)
Base.:/(x::ExpGroup{B},y::ExpGroup{B}) where B = ExpGroup{B}(x.v-y.v)

Base.:*(x::ExpGroup{X},y::ExpGroup{Y}) where {X,Y} = ExpGroup{X*Y}(x.v+y.v)

# other

logdb(x::AbelianGroup) = log(exp10(0.1),x)

Base.one(g::AbelianGroup) = Group(zeros(Values{dimension(g),Int}),1,name(g))
Base.isone(x::Group) = iszero(norm(x.v)) && isone(x.c)
Base.isone(x::AbelianGroup) = false
Base.zero(x::AbelianGroup) = log(one(x))
Base.iszero(x::AbelianGroup) = false
Base.iszero(x::LogGroup) = isone(value(x))

Base.:(==)(g::Group,f::Float64) = product(g) == f
Base.:(==)(f::Float64,g::Group) = product(g) == f

Base.:-(g::Group) = Group(g.v,-g.c,valname(g))

coefprod(a,b) = a*b
coefprod(a::FieldConstants.Constant,b) = a*Constant(b)
coefprod(a,b::FieldConstants.Constant) = Constant(a)*b
coefprod(a::FieldConstants.Constant,b::FieldConstants.Constant) = a*b
Base.:*(a::Group{G,T,S,N} where {T,S},b::Group{G,T,S,N} where {T,S}) where {N,G} = Group(a.v+b.v,coefprod(coef(a),coef(b)),Val(G))
Base.:/(a::Group{G,T,S,N} where {T,S},b::Group{G,T,S,N} where {T,S}) where {N,G} = Group(a.v-b.v,coefprod(coef(a),inv(coef(b))),Val(G))
Base.:^(a::Group,b::Number) = Group(b*a.v,coef(a)^b,valname(a))
Base.:^(a::Group,b::Integer) = Group(b*a.v,coef(a)^b,valname(a))
Base.:^(a::Group,b::Rational) = Group(b*a.v,coef(a)^b,valname(a))
Base.:^(::Constant{a},b::Group) where a = Constant(a^b)
Base.sqrt(a::Group{G,T}) where {G,T} = Group{G,T}(a.v/2,sqrt(coef(a)))
Base.sqrt(a::Group{G,Int}) where G = Group{G,Rational{Int}}(a.v//2,sqrt(coef(a)))
Base.cbrt(a::Group{G,T}) where {G,T} = Group{G,T}(a.v/3,cbrt(coef(a)))
Base.cbrt(a::Group{G,Int}) where G = Group{G,Rational{Int}}(a.v//3,cbrt(coef(a)))
Base.inv(a::Group{G,T}) where {G,T} = Group{G,T}(-a.v,inv(coef(a)))

@pure valueat(::Val{j},::Val{k},::Val{name}) where {j,k,name} = valueat(j,k,name)
valueat(j,k,n,z::T=1) where T = Group{n,T,Int,k}(Values{k,T}([i==j ? z : 0 for i ∈ 1:k]),1)
Base.:*(a::Number,b::Group{G,T,S,N}) where {G,T,S,N} = times(factorize(a,Val(G)),b)
Base.:*(a::Group{G,T,S,N},b::Number) where {G,T,S,N} = times(a,factorize(b,Val(G)))
Base.:*(a::Constant,b::Group{G,T,S,N}) where {G,T,S,N} = FieldConstants.param(a)*b
Base.:*(a::Group{G,T,S,N},b::Constant) where {G,T,S,N} = a*FieldConstants.param(b)
Base.:/(a::Number,b::Group) = a*inv(b)#
Base.:/(a::Group{G,T,S,N},b::Number) where {G,T,S,N} = times(a,inv(factorize(b,Val(G))))#

times(a::Group,b::Group) = a*b
times(a::Number,b::Group{G,T,S,N}) where {G,T,S,N} = Group{G,T}(b.v,coefprod(a,coef(b)))
times(a::Group{G,T,S,N},b::Number) where {G,T,S,N} = Group{G,T}(a.v,coefprod(coef(a),b))

#####

@pure basistext(x::Group{G,T,S,N} where {G,T,S}) where N = letters(N)
printdims(io::IO,x::Group) = printdims(io,x,basistext(x))

using SyntaxTree

symbols(x::Vector{Symbol}) = Values{length(x)}(x)
symbols(x::Vector) = Values{length(x)}(symbol.(x))
symbol(x::Expr) = x.head == :call ? x.args[2] : x.args[1]
symbol(x::Symbol) = x
#symbol(x::Number) = Symbol(string(x))

valbols(x::Vector) = Values{length(x)}(valbol.(x))
valbol(x::Expr) = x.head == :call ? x.args[3] : x.args[2]

strchar(x::AbstractVector) = strchar(string.(x))
strchar(x::AbstractVector{String}) = prod(length.(x).==1) ? getindex.(x,Ref(1)) : x

checkassign(x) = true
checkassign(x::Expr) = x ≠ :(Base.MathConstants.ℯ)
checkassign(x::Number) = false

checkmeasure(x) = false
checkmeasure(x::Expr) = x.head == :call && x.args[1] == :≈
checkint2(x::Number) = isinteger(x)
checkint2(x) = false
gen(in,dex) = Expr(:call,:*,[:($(in[i])^makeint(g.v[$(dex[i])])) for i ∈ 1:length(in)]...)

checksym(x::Symbol) = true
checksym(x::Number) = true
checksym(x) = false

checkdiv(x::Expr) = x.head == :call ? (x.args[1] == :≡ || (x.args[1] ≠ :≈ && checkdiv(x.args[3]))) : false
checkdiv(x::Number) = isinteger(x)
checkdiv(x) = false

export @group, @ring

@pure product(::Constant{N}) where N = product(N)
hasproduct(x::LogGroup) = hasproduct(x.v)
hasproduct(x::ExpGroup) = hasproduct(x.v)
factorize(x,G) = x
Base.float(x::Group) = product(x)

macro ring(arg...)
    group(:Ring,arg...)
end
macro group(arg...)
    group(:Constant,arg...)
end
function group(fun,arg...)
    args = length(arg)==2 ? linefilter!(arg[2]).args : collect(arg[2:end])
    vargs = symbols(args)
    N,G = length(args),QuoteNode(arg[1])
    hasval = !prod(checksym.(args))
    def = if hasval
        vals = valbols(args)
        cm = checkmeasure.(args)
        fcm = findall(cm)
        fncm = findall(.!cm)
        ci = checkint2.(vals[fncm])
        fci = fncm[findall(ci)]
        val = isempty(fci) ? :(g.c) : Expr(:call,:*,gen(float.(vals[fci]),fci),:(measure(g.c)))
        fnci = fncm[findall(.!ci)]
        val = isempty(fnci) ? val : Expr(:call,:*,gen(vals[fnci],fnci),val)
        val = isempty(fcm) ? val : quote
            out = $val
            if iszero($(Expr(:call,:+,[:(abs(g.v[$i])) for i ∈ fcm]...)))
                out
            else
                $(Expr(:call,:*,:out,gen(vals[fcm],fcm)))
            end
        end
        val = Expr(:function,:(FieldAlgebra.product(g::Group{$G,T,S,$N}) where {T,S}),val)
        faci = findall(checkint2.(vals))
        facd = findall(checkdiv.(args))
        va = [valueat(i,N,arg[1]) for i ∈ faci]
        vad = [valueat(i,N,arg[1]) for i ∈ facd]
        Expr(:block,val,
            Expr(:function,:(FieldAlgebra.factorize(x::Int,::Val{$G})),
                Expr(:block,:(ex = zeros(Variables{$(length(faci)),Int})),
                    [:((x,ex[$i]) = FieldAlgebra.factorfind(x,$(Int(vals[faci[i]])))) for i ∈ 1:length(faci)]...,
                    Expr(:call,:*,:(Group($(zeros(Values{N,Int})),x,$(Val(arg[1])))),
                        [:($(va[i])^ex[$i]) for i ∈ 1:length(faci)]...))),
            Expr(:function,:(FieldAlgebra.factorize(x::Float64,::Val{$G})),
                Expr(:block,quote
                    if isinteger(x)
                        try
                            return FieldAlgebra.factorize(Int(x),$(Val(arg[1])))
                        catch
                        end
                    end end,
                    :(ex = zeros(Variables{$(length(facd)),Int})),
                    [:((x,ex[$i]) = FieldAlgebra.factorfind(x,$(vals[facd[i]]))) for i ∈ 1:length(facd)]..., # todo: factorize x if integer(x)
                    Expr(:call,:*,:(Group($(zeros(Values{N,Int})),x,$(Val(arg[1])))),
                        [:($(vad[i])^ex[$i]) for i ∈ 1:length(facd)]...))))
    else
        nothing
    end
    out = quote
        FieldAlgebra.basistext(::Group{$G,T,S,$N} where {T,S}) = $(strchar(vargs))
        FieldAlgebra.hasproduct(g::Group{$G,T,S,$N}) where {T,S} = $hasval
        $([:($(esc(vargs[i])) = $fun(valueat($i,$N,$G))) for i ∈ findall(checkassign.(vargs))]...)
        $def
    end
    return out #QuoteNode(out)
end

factorfind(x,k,i=0) = iszero(x) ? (x,0) : (r = x%k; iszero(r) ? factorfind(x÷k,k,i+1) : (x,i))

const aa,bb,cc = 2,3,5
const isq = Values('F','M','L','T','Q','Θ','N','J','A','R','C')
#=const dims = length(isq)
#factorfind(x,k,i=0) = iszero(x) ? (x,0) : (r = x%k; iszero(r) ? factorfind(x÷k,k,i+1) : (x,i))

const 𝟙 = valueat(0,dims)
for i ∈ 1:dims
    @eval const $(Symbol(isq[i])) = valueat($i,dims)
end
const usq = Values(F,M,L,T,Q,Θ,N,J,A,R,C)=#

include("ring.jl")

end # module
