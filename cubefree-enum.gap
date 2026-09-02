###
### cubefree-enum.gap
###
### The number of isomorphism types of groups of a cubefree order n.
###
### This file implements Theorem 4.11 of the paper
###
###   The number of groups of cubefree order
###
###   Heiko Dietrich, David Jefferies
###   arxiv: https://arxiv.org/abs/2608.18815
###
###
### This final implementation has been completely rewritten and improved by the LLM Claude Opus 5.
### This implementation has been cross-checked extensively, see Section 6.3.
###
###
### The main function is
###
###    NumberCubefreeGroups(n)   (called gnu(n) in Theorem 4.11)  for a cubefree n
###
### which runs over the three sums  s in S(n),  d | Q(n/s),  l | n/(sd)  of the
### theorem and, for each triple (s,d,l), evaluates gnu_Phi(n/(sd),l) by one of
###
###    cf_gnu_phi_0(n,l)       gnu_Phi(n,l) if t = v_2(n/l) = 0    Corollary 3.11
###    cf_gnu_phi_1(n,l)       gnu_Phi(n,l) if t = v_2(n/l) = 1    Proposition 4.7
###    cf_gnu_phi_2(n,l)       gnu_Phi(n,l) if t = v_2(n/l) = 2    Proposition 4.10
###
### The function cf_clearcache() empties the four caches used by these functions,
### see the comment at cf_clearcache.
###
### Section 8 adds the two restricted counts of Remark 4.14,
###
###    NumberCubefreeSolvableGroups(n)        gnu_solv(n)
###    NumberCubefreeSupersolvableGroups(n)   gnu_ssolv(n)
###
### with their own cache, emptied by cf_ss_clearcache().
###
### Section 9 adds the count
###
###    NumberCubefreeCGroups(n)                gnu_cyc(n)
###
### of the groups all of whose Sylow subgroups are cyclic; it needs no cache of
### its own, since it reuses the sets U(p,e,L) of Sections 2 and 6.
###
### usage:  Read("cubefree-enum.gap");
###         NumberCubefreeGroups(2^2*3^2*5^2*7^2);
###
### Before the sums of Theorem 4.11 are evaluated, n is split by the coprime
### reduction of Remark 3.16: the prime divisors of n are the vertices of the
### graph Gamma(n) (cf_edge, cf_components) and gnu(n) is the product of the
### gnu(n_C) over the connected components C of Gamma(n). The evaluation of
### Theorem 4.11 itself happens in cf_gnu_connected.
###
### The functions cf_gnu_phi_t follow the statements of Corollary 3.11 and
### Propositions 4.7 and 4.10 line by line, but they evaluate them as described in
### Section 6.2 of the paper.  The sets U(p,e,L) of (3.2) depend neither on s nor
### on d or l, so they are computed once and cached (cf_Udata); only the integers
### (j,d,d^+,d^-) attached to a U ever reach the local numbers, so the U with
### equal data are merged and counted with a multiplicity; a pair (l,L) whose term
### vanishes for a local reason is recognised before any projection tuple is built
### (cf_feasible); and the products of Lemmas 3.12, 3.13 and A.1 are accumulated
### in a single pass over the columns, with c,z,g,r read off lookup tables
### (cf_KqtB, cf_KqH).  The prime factorisations of the socle orders, the sets
### A(n) of Definition 2.1 and the lookup tables themselves are cached as well,
### since they are re-derived for every (s,d,l) triple, and there are
### Sum_{d | Q(n)} tau(n/d) such triples per simple factor.
###
### The inner sums over xi in Theta(U), alpha in Aut(E) and psi in Hom(E,Theta(U))
### of Propositions 4.7 and 4.10 are exponential in the number r of columns with
### Theta(U) <> 1, although most of their terms vanish.  Section 5 replaces them
### by a backtracking enumeration of the column characters that enters only the
### branches which Lemma A.1 does not force to zero; this is the second
### optimisation described in Section 6.2 of the paper.
###



######################################################
##
## 1.  Arithmetic helpers: Definition 2.1
##

#####################################################
## input: integer n and prime q
## output: min(v_q(n),2), capped at 2 since this is all that is needed below
##         (also for n = p-1 or p^2-1, and for t = v_2(n/l))
##
cf_vq := function(n, q)
   if not n mod q = 0 then return 0; fi;
   if n mod q^2 = 0 then return 2; fi;
   return 1;
end;

#####################################################
## input: cubefree n
## output: Q(n), the product of the primes p with p^2 | n
##
cf_Q := function(n)
local facs;
   facs := Filtered(Collected(FactorsInt(n)), x-> x[2] = 2);
   if facs = [] then return 1; fi;
   return Product(facs, x-> x[1]);
end;

#####################################################
## input: primes p <> q with p^ep || n and q^eq || n
## output: true iff p and q are joined in the graph Gamma(n) of Remark 3.16,
##         that is, iff p | q^i-1 for some i <= eq, or q | p^j-1 for some j <= ep
##
cf_edge := function(p, ep, q, eq)
   if (q-1) mod p = 0 then return true; fi;
   if (p-1) mod q = 0 then return true; fi;
   if eq = 2 and (q+1) mod p = 0 then return true; fi;
   if ep = 2 and (p+1) mod q = 0 then return true; fi;
   return false;
end;

#####################################################
## input: cubefree n
## output: the list of the n_C, where C runs over the connected components of
##         the graph Gamma(n) and n_C is the C-part of n; the n_C
##         are pairwise coprime with product n, and Remark 3.16 gives
##         gnu(n) = product of the gnu(n_C).  The components are found by label
##         propagation on the (at most 15 for n < 10^18) prime divisors of n.
##
cf_components := function(n)
local facs, m, lab, ch, i, j, lo, hi, k, res, c;
   facs := Collected(FactorsInt(n));
   if n = 1 then return []; fi;
   if IsEvenInt(n) then return [n]; fi;
   m    := Length(facs);
   lab  := [1..m];
   repeat
      ch := false;
      for i in [1..m] do
         for j in [i+1..m] do
            if not lab[i] = lab[j]
               and cf_edge(facs[i][1], facs[i][2], facs[j][1], facs[j][2]) then
               lo := Minimum(lab[i], lab[j]);
               hi := Maximum(lab[i], lab[j]);
               for k in [1..m] do
                  if lab[k] = hi then lab[k] := lo; fi;
               od;
               ch := true;
            fi;
         od;
      od;
   until not ch;
   res := [];
   for c in Set(lab) do
      Add(res, Product(Filtered([1..m], i-> lab[i] = c), i-> facs[i][1]^facs[i][2]));
   od;
   return res;
end;

#####################################################
## input: integer n
## output: S(n), the orders of the cubefree simple groups dividing n, and 1
##
cf_S := function(n)
local res, p, a;
   res := [1];
   for p in PrimeDivisors(n) do        # p divides p(p^2-1)/2, hence p | n
      if p > 3 then
         a := p*(p^2-1)/2;
         if n mod a = 0 then Add(res, a); fi;
      fi;
   od;
   return res;
end;

#####################################################
## input: cubefree n
## output: A(n), the abelian groups of order n, as records rec(primes,sylow)
##         where sylow[k] is [1,1], [2,1] or [2,2] for a Sylow subgroup
##         C_q, C_{q^2} or C_q x C_q at the prime q = primes[k]
##
## Cache for Collected(FactorsInt(x)) on the divisors of n: the socle order l
## and the acting order nu are re-derived for every (s,d,l) triple of
## Theorem 4.11, so their factorisations are computed once and reused.
##
cf_faccache := NewDictionary([1,1], true);;

cf_facs := function(x)
local v;
   v := LookupDictionary(cf_faccache, [x]);
   if not v = fail then return v; fi;
   v := Collected(FactorsInt(x));
   AddDictionary(cf_faccache, [x], v);
   return v;
end;

## Cache for A(n); the records it returns are read-only for all callers.  The
## empty case n = 1 is not cached, since the caller would then share one record.
##
cf_Acache := NewDictionary([1,1], true);;

cf_A := function(n)
local facs, res, i, pr, v;
   v := LookupDictionary(cf_Acache, [n]);
   if not v = fail then return v; fi;
   facs := cf_facs(n);
   if facs = [[1,1]] then return [ rec(primes:=[], sylow:=[]) ]; fi;   # n = 1

   res  := [];
   for i in facs do
      if i[2] = 1 then Add(res, [[1,1]]); else Add(res, [[2,1],[2,2]]); fi;
   od;
   pr  := List(facs, x-> x[1]);
   v   := List(Cartesian(res), l-> rec(primes := pr, sylow := l));
   AddDictionary(cf_Acache, [n], v);
   return v;
end;

# the largest j with C_{q^j} a quotient of the Sylow subgroup given by Lq
cf_largestCyclicQuot := function(Lq)
   if Lq = [2,1] then return 2; else return 1; fi;
end;


######################################################
##
## 2.  The canonical projections U(p,e,L): Definitions 3.2, 3.4 and 4.6
##
## Every U in U(p,e,L) is stored as a record
##
##      rec( theta, typ, delta, loc )
##
## where theta = |Theta(U)| in {1,2} (Lemma 3.5), typ in {0,...,5} is the column
## type of Definition 4.6, delta = 1 iff 4 | p-1, and loc[k] = rec(j,d,dp,dm)
## holds the data of the Sylow q-subgroup U_q for q = L.primes[k]: its order is
## q^j, its rank is d, and (dp,dm) are the ranks of the eigenspaces of the
## generator theta_U of Theta(U) as in Lemma 3.13.  These integers are all that
## the formulas of Lemmas 3.12, 3.13 and A.1 ever use.
##

### The subgroups of D(p)_q are stored as records rec(j,d,gens) of order q^j and
### rank d, where gens is a canonical generating set in C_{q^b} x C_{q^b} and q^b
### is the largest q-power dividing p-1 (capped at q^2).  The entries of a pair
### are exponents with respect to a fixed generator zeta of the q-part of F_p^*,
### so [x,y] denotes diag(zeta^x, zeta^y); in particular [1,y] has a first entry
### of full order q^b, and the identity in a coordinate is the exponent 0.
### Replacing a generator by a power of itself with unit exponent does not change
### the subgroup, so the normal form divides through by whichever coordinate is a
### unit.  With s = q^(b-1) the shapes are
###    trivial           gens = [ ]
###    order q           gens = [ s*[1,k] ], 0<=k<q, or [ [0,s] ]
###    cyclic, order q^2 gens = [ [1,y] ], 0<=y<q^2, or [ [x,1] ] with q | x
###    C_q x C_q         gens = [ [s,0], [0,s] ]
### The two shapes in the third row are the two cases of that division: [1,y] is
### diag of order q^2 times order dividing q^2, while [x,1] with q | x is diag of
### order dividing q times order q^2, whose first exponent cannot be scaled to 1.
### They give q^2 + q = (q^4-q^2)/phi(q^2) subgroups, as they must.
### These normal forms are unique, so two subgroups are equal iff their gens are.

# swaps the two coordinates of every generator
cf_swap := H -> List(H, x-> [x[2],x[1]]);

# H is scalar iff all of its generators are
cf_isScalar := H -> ForAll(H.gens, g-> g[1] = g[2]);

# the image of H under the swap J, again in normal form
cf_swapSub := function(H, q, b)
local qb, s, g, x, y;
   if H.d = 0 or H.d = 2 then return H; fi;
   qb := q^b;  s := q^(b-1);
   g  := cf_swap(H.gens)[1];
   x  := g[1];  y := g[2];
   if H.j = 1 then
      x := (x/s) mod q;  y := (y/s) mod q;
      if x = 0 then return rec(j:=1, d:=1, gens:=[[0,s]]); fi;
      return rec(j:=1, d:=1, gens:=[[s, (s*QuotientMod(y,x,q)) mod qb]]);
   fi;
   if x mod q = 0 then return rec(j:=2, d:=1, gens:=[[QuotientMod(x,y,qb),1]]); fi;
   return rec(j:=2, d:=1, gens:=[[1, QuotientMod(y,x,qb)]]);
end;

# the ranks of the two eigenspaces of the swap on a swap-invariant H;
# on a cyclic H the swap acts as the identity or as inversion (Lemma 3.7)
cf_eigen := function(H, q, b)
local qb;
   if H.d = 0 then return [0,0]; fi;
   if H.d = 2 then return [1,1]; fi;
   qb := q^b;
   if cf_swap(H.gens)[1] = H.gens[1] mod qb then return [1,0]; fi;
   return [0,1];
end;

#####################################################
## input: prime q, integer b >= 0, Sylow data Lq
## output: the subgroups of D(p)_q that are quotients of the Sylow subgroup Lq,
##         where q^b is the largest q-power dividing p-1 (capped at q^2)
##
cf_Dsubgroups := function(q, b, Lq)
local qb, s, res, k, x, y;
   res := [ rec(j:=0, d:=0, gens:=[]) ];
   if b = 0 then return res; fi;
   qb := q^b;  s := q^(b-1);
   for k in [0..q-1] do Add(res, rec(j:=1, d:=1, gens:=[[s,(s*k) mod qb]])); od;
   Add(res, rec(j:=1, d:=1, gens:=[[0,s]]));
   if Lq = [2,2] then Add(res, rec(j:=2, d:=2, gens:=[[s,0],[0,s]])); fi;
   if Lq = [2,1] and b = 2 then
      for y in [0..q^2-1]   do Add(res, rec(j:=2, d:=1, gens:=[[1,y]])); od;
      for x in [0,q..q^2-q] do Add(res, rec(j:=2, d:=1, gens:=[[x,1]])); od;
   fi;
   return res;
end;

#####################################################
## input: prime p, e in {1,2}, abelian group record L
## output: U(p,e,L) of (3.2), as a list of records rec(theta,typ,delta,loc)
##
cf_Upel := function(p, e, L)
local nq, res, opts, bs, tup, sw, th, loc, k, d, ee, sc, delta, typ;
   nq := Length(L.primes);  res := [];
   delta := 0;  if not p = 2 and (p-1) mod 4 = 0 then delta := 1; fi;

   ## e = 1: the subgroups C(p,b) of GL_1(p); here Theta(U) = 1 and the column
   ## has type (1), or type (0) if p = 2
   if e = 1 then
      if p = 2 then typ := 0; else typ := 1; fi;
      opts := List([1..nq], k-> [0..Minimum(cf_largestCyclicQuot(L.sylow[k]),
                                            cf_vq(p-1,L.primes[k]))]);
      for tup in Cartesian(opts) do
         loc := List([1..nq], k-> rec(j:=tup[k], d:=Minimum(tup[k],1),
                                      dp:=Minimum(tup[k],1), dm:=0));
         Add(res, rec(theta:=1, typ:=typ, delta:=delta, loc:=loc));
      od;
      return res;
   fi;

   ## e = 2, reducible: one subgroup from each swap orbit on the subgroups of
   ## D(p); Theta(U) <> 1 iff U is swap invariant and non-scalar (Lemma 3.5),
   ## and the column has type (2), (3) or (4)
   bs   := List([1..nq], k-> cf_vq(p-1,L.primes[k]));
   opts := List([1..nq], k-> cf_Dsubgroups(L.primes[k], bs[k], L.sylow[k]));
   for tup in Cartesian(opts) do
      sw := List([1..nq], k-> cf_swapSub(tup[k], L.primes[k], bs[k]));
      if List(sw,u->u.gens) < List(tup,u->u.gens) then continue; fi;
      sc := ForAll(tup, cf_isScalar);
      if List(sw,u->u.gens) = List(tup,u->u.gens) and not sc
         then th := 2; else th := 1; fi;
      if sc then typ := 2; elif th = 2 then typ := 4; else typ := 3; fi;
      loc := [];
      for k in [1..nq] do
         if th = 2 then ee := cf_eigen(tup[k], L.primes[k], bs[k]);
                   else ee := [tup[k].d, 0]; fi;
         Add(loc, rec(j:=tup[k].j, d:=tup[k].d, dp:=ee[1], dm:=ee[2]));
      od;
      Add(res, rec(theta:=th, typ:=typ, delta:=delta, loc:=loc));
   od;

   ## e = 2, irreducible: U = Sigma(p,b) with b not dividing p-1; here Theta(U)
   ## has order 2 and the column has type (5).  The generator theta_U is trivial
   ## on U_q if |U_q| divides p-1, and is inversion if |U_q| divides p+1.
   opts := List([1..nq], k-> [0..Minimum(cf_largestCyclicQuot(L.sylow[k]),
                                         cf_vq(p^2-1,L.primes[k]))]);
   for tup in Cartesian(opts) do
      if ForAll([1..nq], k-> tup[k] <= cf_vq(p-1,L.primes[k])) then continue; fi;
      loc := [];
      for k in [1..nq] do
         d := Minimum(tup[k],1);
         if tup[k] <= cf_vq(p-1,L.primes[k])
            then Add(loc, rec(j:=tup[k], d:=d, dp:=d,  dm:=0));
            else Add(loc, rec(j:=tup[k], d:=d, dp:=0, dm:=d)); fi;
      od;
      Add(res, rec(theta:=2, typ:=5, delta:=delta, loc:=loc));
   od;

   return res;
end;

#####################################################
## the cache for U(p,e,L), collapsed to its distinct records with multiplicities;
## the key is a flat list of integers, with the Sylow data [1,1], [2,1], [2,2]
## of L encoded as 3, 5, 6
##
## Section 6.2 of the paper: U(p,e,L) depends only on (p,e,L) -- not on the
## simple factor s, the Frattini order d or the socle order l -- and only the record
## rec(theta,typ,delta,loc) of a U is ever used, so equal records are merged.
##
cf_cache := NewDictionary([1,1], true);;

cf_Udata := function(p, e, L)
local val, key, k;
   key := [p, e];
   for k in [1..Length(L.primes)] do
      Add(key, L.primes[k]);
      Add(key, 2*L.sylow[k][1] + L.sylow[k][2]);
   od;
   val := LookupDictionary(cf_cache, key);
   if not val = fail then return val; fi;
   val := Collected(cf_Upel(p, e, L));
   AddDictionary(cf_cache, key, val);
   return val;
end;

## the cache for the lookup tables of Section 3, declared here so that
## cf_clearcache can reach it; it is a plain list indexed by the prime q
cf_tabcache := [];;
cf_tabmax   := 100000;;

## None of the four caches depends on n -- U(p,e,L) depends only on (p,e,L), and
## the other three only on their argument -- so they stay sound across different
## n and keep paying off in a sweep over many orders.  They do grow; call this to
## reclaim the memory.
cf_clearcache := function()
   cf_cache    := NewDictionary([1,1], true);
   cf_faccache := NewDictionary([1,1], true);
   cf_Acache   := NewDictionary([1,1], true);
   cf_tabcache := [];
   return;
end;

#####################################################
## input: the columns cols = [[p,e],...] of a socle order l, abelian type L
## output: false if the term of (l,L) vanishes because some prime q dividing |L|
##         cannot be realised in any column, true otherwise
##
## Section 6.2 of the paper: for a column (p,e) the q-part of a projection U is
## cyclic of order at most q^mj with mj = min(v_q(p-1 resp. p^2-1), largest cyclic
## quotient of L_q), and it has rank 2 only inside D(p)_q, which needs q | p-1.  Since
## every K_q is isomorphic to L_q and projects onto all these q-parts, L_q must
## fit into their product.
##
cf_feasible := function(cols, L)
local k, q, Lq, mj, md, x, bq, j, lcq;
   for k in [1..Length(L.primes)] do
      q := L.primes[k];  Lq := L.sylow[k];
      mj := 0;  md := 0;
      lcq := cf_largestCyclicQuot(Lq);          # independent of the column
      for x in cols do
         if x[2] = 1 then bq := cf_vq(x[1]-1, q); else bq := cf_vq(x[1]^2-1, q); fi;
         j := Minimum(bq, lcq);
         if j > mj then mj := j; fi;
         if j >= 1 then
            if x[2] = 2 and Lq = [2,2] and cf_vq(x[1]-1, q) >= 1
               then md := md + 2;
               else md := md + 1; fi;
         fi;
      od;
      if   Lq = [2,2] then if md < 2 then return false; fi;
      elif Lq = [2,1] then if mj < 2 then return false; fi;
      else                 if mj < 1 then return false; fi;
      fi;
   od;
   return true;
end;


######################################################
##
## 3.  The local numbers |K_q(U,L)^theta| and |K_q(U,L)^H|
##     Lemmas 3.12, 3.13 and A.1
##

#####################################################
## input: prime q
## output: the functions g,c,r,z of Section 3.5 of the paper as lookup lists
##         indexed by argument+1, together with the denominators q-1, q(q-1)
##         and |GL_2(q)|
##
## The table depends on q alone but is asked for once per (s,d,l) triple, L and
## q; the small primes that actually occur are cached in a plain list.
##
cf_tab := function(q)
local t;
   if q <= cf_tabmax and IsBound(cf_tabcache[q]) then return cf_tabcache[q]; fi;
   t := rec(c  := [1, q-1, 0],
            z  := [1, 0, 0],
            g  := [1, q-1, q*(q-1)],
            r  := [1, q^2-1, (q^2-1)*(q^2-q)],
            e1 := q-1,  e2 := q*(q-1),  e3 := (q^2-1)*(q^2-q),  q := q);
   if q <= cf_tabmax then cf_tabcache[q] := t; fi;
   return t;
end;

#####################################################
## input: code typ of L_q (1,2,3 for C_q, C_{q^2}, C_q^2), table tb of cf_tab,
##        projection tuple prof, index k of the prime q
## output: the theta-independent factor of |K_q(U,L)^theta|, that is, the value
##         |K_q(U,L)| of Lemma 3.12
##
## The products over the columns in Lemma 3.12 do not involve theta and are the
## only place where large integers are multiplied, so they are formed once per
## projection tuple rather than once for each of the |Theta(U)| sign vectors.
##
cf_KqtBase := function(typ, tb, prof, k)
local m, i, u, pc, pz, pg, pcj, pr;
   m := Length(prof);
   if typ = 1 then                                    # L_q = C_q
      pc := 1;  pz := 1;
      for i in [1..m] do
         u  := prof[i].loc[k];
         pc := pc * tb.c[u.d+1];
         if u.d > 0 then pz := 0; fi;
      od;
      return (pc - pz)/tb.e1;
   elif typ = 2 then                                  # L_q = C_{q^2}
      pg := 1;  pcj := 1;
      for i in [1..m] do
         u   := prof[i].loc[k];
         pg  := pg  * tb.g[u.j+1];
         pcj := pcj * tb.c[u.j+1];
      od;
      return (pg - pcj)/tb.e2;
   fi;
   pr := 1;  pc := 1;  pz := 1;                       # L_q = C_q x C_q
   for i in [1..m] do
      u  := prof[i].loc[k];
      pr := pr * tb.r[u.d+1];
      pc := pc * tb.c[u.d+1];
      if u.d > 0 then pz := 0; fi;
   od;
   return (pr - (tb.q+1)*pc + tb.q*pz)/tb.e3;
end;

#####################################################
## input: as cf_KqtBase, with theta as a 0/1 vector vx over the columns and the
##        value base of cf_KqtBase for the same (prof,k)
## output: |K_q(U,L)^theta| of Lemma 3.13
##
cf_KqtB := function(typ, tb, prof, vx, k, base)
local m, i, u, pzp, pzm, pcp, pcm, dp, dm;
   m := Length(prof);
   pzp := 1;  pzm := 1;
   for i in [1..m] do
      u := prof[i].loc[k];
      if vx[i] = 0 then
         if u.d  > 0 then pzp := 0; fi;
      else
         if u.dp > 0 then pzp := 0; fi;
         if u.dm > 0 then pzm := 0; fi;
      fi;
   od;
   if typ < 3 then return (pzm + pzp) * base; fi;
   pcp := 1;  pcm := 1;
   for i in [1..m] do
      u := prof[i].loc[k];
      if vx[i] = 0 then dp := u.d;  dm := 0;
                   else dp := u.dp; dm := u.dm; fi;
      pcp := pcp * tb.c[dp+1];
      pcm := pcm * tb.c[dm+1];
   od;
   return (pzm + pzp)*base + ((pcp - pzp)/tb.e1)*((pcm - pzm)/tb.e1);
end;

#####################################################
## input: code typ of L_q, table tb of cf_tab, projection tuple prof, index k of
##        the prime q, and a GF(2)-basis of a subgroup H of Theta(U) (each basis
##        vector is a 0/1 list over the columns)
## output: |K_q(U,L)^H| of Lemma A.1
##
## The set Y of Lemma A.1 is built on the fly: the character lambda_i of the
## i-th column is encoded as the integer whose bits are the entries of the basis
## vectors at i, the class "+" is present iff some column contributes to W^+,
## and a class chi <> "+" is present iff some column with character chi has
## d_i^- <> 0.  As in cf_KqtB the products are accumulated in one pass.
##
cf_KqH := function(typ, tb, prof, k, lams, base)
local m, i, lam, has0, chs, nch, cc, pc, pz, res, u, d;
   m := Length(prof);
   has0 := false;  chs := [];
   for i in [1..m] do
      u   := prof[i].loc[k];
      lam := lams[i];
      if lam = 0 then                                 # H acts trivially on X_i
         if u.d > 0 then has0 := true; fi;
      else
         if u.dp > 0 then has0 := true; fi;
         if u.dm > 0 and not lam in chs then Add(chs, lam); fi;
      fi;
   od;
   nch := Length(chs);  if has0 then nch := nch + 1; fi;

   if nch <= 1 then return base; fi;                  ## |K_q(U,L)^H| = |K_q(U,L)|
   if nch > 2 or not typ = 3 then return 0; fi;

   if has0 then chs := Concatenation([0], chs); fi;   ## Y = {chi,chi'}: Lambda Lambda'
   res := 1;
   for cc in chs do
      pc := 1;  pz := 1;
      for i in [1..m] do
         u := prof[i].loc[k];
         if cc = 0 then
            if lams[i] = 0 then d := u.d; else d := u.dp; fi;
         elif lams[i] = cc then d := u.dm;
         else d := 0; fi;
         pc := pc * tb.c[d+1];
         if d > 0 then pz := 0; fi;
      od;
      res := res * (pc - pz)/tb.e1;
   od;
   return res;
end;

#####################################################
## input: projection tuple prof, the codes typs and tables tabs of the primes q
##        dividing nu_0, a GF(2)-basis of a subgroup H of Theta(U)
## output: |K(U,L)^H| = prod_{q | nu_0} |K_q(U,L)^H|, see Appendix A
##
cf_KUL := function(prof, typs, tabs, lams, bs)
local prod, k;
   prod := 1;
   for k in [1..Length(typs)] do
      prod := prod * cf_KqH(typs[k], tabs[k], prof, k, lams, bs[k]);
      if prod = 0 then return 0; fi;
   od;
   return prod;
end;


######################################################
##
## 4.  The column numbers A(U;xi,psi) and T(U;P,xi,alpha,psi), and the numbers
##     A(U;E,xi,alpha,psi):  Lemmas 4.8, A.5 and A.2
##

#####################################################
## input: column type typ of U, xi in Theta(U) and psi in Theta(U), both encoded
##        as 0 (trivial) or 1 (nontrivial)
## output: A(U;xi,psi), the table of Lemma 4.8
##
## A dash in that table means that the pair (xi,psi) does not exist because
## Theta(U) = 1, which happens exactly for the types (0)-(3); the caller only
## produces xi = psi = 0 for those columns.
##
cf_Atab := function(typ, xi, psi)
   if not psi = 0 then return 1; fi;                  # types (4),(5) only
   if not xi  = 0 then return 2; fi;                  # types (4),(5) only
   return [1,2,3,4,4,2][typ+1];
end;

#####################################################
## The functions varphi_a, varphi_{a+abar}, varphi^-_{a+abar} and rho of
## Definition A.3, with the values of Lemma A.4 and Table 3.
##
## P is one of "1", "C2", "C4", "V4"; for P = "C4" the automorphism al = 0 is the
## identity and al = 1 is inversion, and for P = "V4" the classes al = 0,1,2 are
## the identity, a transposition and a 3-cycle.  The argument delta is the flag
## Delta_{4 | p-1} stored in the column record.
##

cf_phia := function(P, al, delta)       # varphi_a
   if P = "1"  then return 1; fi;
   if P = "C2" then return 2; fi;
   if P = "C4" then if al = 0 then return 2+2*delta; else return 2; fi; fi;
   return [4,2,1][al+1];
end;

cf_phic := function(P, al)              # varphi_{a+abar}
   if P = "1"  then return 1; fi;
   if P = "C2" then return 2; fi;
   if P = "C4" then if al = 0 then return 4; else return 2; fi; fi;
   return [4,2,1][al+1];
end;

cf_phim := function(P, al)              # varphi^-_{a+abar}
   if P = "1"  then return 1; fi;
   if P = "C2" then return 2; fi;
   if P = "C4" then if al = 0 then return 2; else return 4; fi; fi;
   return [4,2,1][al+1];
end;

cf_rho := function(P, al, delta)        # rho
   if P = "1"  then return 1; fi;
   if P = "C2" then return 3; fi;
   if P = "C4" then if al = 0 then return 4+6*delta; else return 4; fi; fi;
   return [10,4,1][al+1];
end;

# the class of alpha^2: inversion^2 = id, transposition^2 = id, 3-cycle^2 = 3-cycle
cf_alsq := function(P, al)
   if P = "V4" and al = 2 then return 2; fi;
   return 0;
end;

#####################################################
## input: the record u of a column U, a group P of order dividing 4, xi in
##        Theta(U), the class al of alpha in Aut(P), and pnz = 1 if psi <> 1
## output: T(U;P,xi,alpha,psi) of Lemma A.5
##
## For psi <> 1 the lemma also requires psi o alpha = psi; this is a condition on
## all columns at once and is imposed by the caller.
##
cf_T := function(u, P, xi, al, pnz)
   if pnz = 1 then
      if u.typ < 4 then return 0; fi;
      if P = "C2" then return 1; else return 2; fi;   # |Hom(ker psi, C_{2^a})|
   fi;
   if P = "1" or u.typ = 0 then return 1; fi;
   if u.typ = 1 then return cf_phia(P, al, u.delta); fi;
   if u.typ = 2 then return cf_rho(P, al, u.delta); fi;
   if u.typ = 3 then return cf_phia(P, al, u.delta)^2; fi;
   if u.typ = 4 then
      if xi = 0 then return cf_phia(P, al, u.delta)^2; fi;
      return cf_phia(P, cf_alsq(P,al), u.delta);
   fi;
   if xi = 0 or u.delta = 1 then return cf_phic(P, al); fi;
   return cf_phim(P, al);
end;

#####################################################
## input: the record u of a canonical projection U
## output: the numbers T(U;P,xi,alpha,psi) of Lemma A.5 that cf_h needs, as
##         tab[xi+1][pnz+1] = [ C2, C4 (al=0,1), V4 (al=0,1,2) ]
##
## These depend only on the column data u, not on the projection tuple or on the
## pair (xi,psi) beyond the two flags, so they are computed once per canonical
## projection and stored in u; the records of cf_Udata are cached, hence so are
## the tables.
##
cf_Ttab := function(u)
local xi, pn, t;
   if IsBound(u.ttab) then return u.ttab; fi;
   t := [];
   for xi in [0,1] do
      t[xi+1] := [];
      for pn in [0,1] do
         t[xi+1][pn+1] := [ cf_T(u, "C2", xi, 0, pn),
                            cf_T(u, "C4", xi, 0, pn), cf_T(u, "C4", xi, 1, pn),
                            cf_T(u, "V4", xi, 0, pn), cf_T(u, "V4", xi, 1, pn),
                            cf_T(u, "V4", xi, 2, pn) ];
      od;
   od;
   u.ttab := t;
   return t;
end;

#####################################################
## input: E = "C4" or "V4", projection tuple prof, xi as a 0/1 vector vx over the
##        columns, the class al of alpha in Aut(E) (for "V4" together with the
##        fixed point kk of alpha on the three involutions, or 0 if there is
##        none), and the images PS of the involutions of E under psi, again as
##        0/1 vectors over the columns; for E = "C4" the list PS has the single
##        entry psi(x) for a generator x of E
## output: A(U;E,xi,alpha,psi) of Lemma A.2
##
## The Moebius sum of Lemma A.2 is evaluated once and for all here:
##
##   E = C4:  R = 1 contributes the product of the T(U_i;C4,...), and R = C_2
##            contributes minus the product of the T(U_i;C2,...); the condition
##            <R>_alpha = C_2 <= ker psi is automatic since Theta(U) has exponent
##            2, and E/C_2 = C_2 with induced automorphism the identity.  The
##            subgroup R = C_4 has mu(R) = 0.
##   E = V4:  R = 1 contributes the product of the T(U_i;V4,...).  An involution
##            R with <R>_alpha = R contributes minus the product of the
##            T(U_i;C2,...) if R <= ker psi, and one with <R>_alpha = E
##            contributes -1 if psi = 1 and 0 otherwise; R = E contributes
##            +2 if psi = 1 and 0 otherwise.  For alpha of order 2 the two moved
##            involutions and R = E cancel; for alpha of order 3 all three
##            involutions are moved, psi = 1 is forced, and the total of the four
##            proper nontrivial R is -1.
##
cf_h := function(E, tt, vx, al, kk, PS)
local m, i, j, pn, h, tw, t, allz;
   m := Length(tt);

   if E = "C4" then
      h := 1;  tw := 1;
      for i in [1..m] do
         t  := tt[i][vx[i]+1][PS[1][i]+1];
         h  := h  * t[2+al];                                # C4, alpha = al
         tw := tw * t[1];                                   # C2
      od;
      return h - tw;
   fi;

   h := 1;  tw := 1;  allz := true;
   for i in [1..m] do
      pn := Maximum(PS[1][i], PS[2][i]);                    # 1 iff psi_i <> 1
      if not pn = 0 then allz := false; fi;
      t  := tt[i][vx[i]+1][pn+1];
      h  := h  * t[4+al];                                   # V4, alpha = al
      tw := tw * t[1];                                      # C2
   od;
   if al = 2 then return h - 1; fi;                         # alpha of order 3
   if al = 1 then                                           # alpha of order 2
      if ForAll(PS[kk], x-> x = 0) then h := h - tw; fi;
      return h;
   fi;
   for j in [1..3] do                                       # alpha = identity
      if ForAll(PS[j], x-> x = 0) then h := h - tw; fi;
   od;
   if allz then h := h + 2; fi;
   return h;
end;



######################################################
##
## 5.  Column characters and their enumeration: Lemma A.1 and Section 6.2
##     of the paper
##
## In gnu_Phi(n,l) with t = v_2(n/l) in {1,2} the inner sums run over xi in
## Theta(U) and psi in Hom(E,Theta(U)).  Both enter the local numbers only
## through the character lambda_i that the subgroup H = <xi, psi(E)> induces on
## the i-th column, encoded as an integer:
##
##      t = 1:   lambda_i = xi_i + 2 psi_i                in [0..3]
##      t = 2:   lambda_i = xi_i + 2 psi^1_i + 4 psi^2_i  in [0..7]
##
## Columns with Theta(U) = 1 always have lambda_i = 0.  By Lemma A.1 (cf_KqH)
## the factor |K_q(U,L)^H| is zero as soon as the columns carry, at the prime q,
## more than two classes, or exactly two while L_q is not C_q x C_q.  The class
## count is monotone in the set of columns already assigned -- has0 only turns
## from false to true and the list chs of classes only grows -- so a partial
## assignment that violates the bound can never be repaired.  The characters can
## therefore be enumerated by backtracking, and only the branches that survive
## are entered.  A direct evaluation of the two propositions instead sweeps all
## 4^r resp. 6*8^r pairs (xi,psi), where r is the number of columns with
## Theta(U) <> 1, and discovers the zeros only at the leaves; this is what
## cf_gnu_phi_1_OLD and cf_gnu_phi_2_OLD of Section 10 do.
##
## A second saving in the case t = 2: a direct evaluation loops over alpha in
## Aut(E) outside psi and then skips the psi with psi o alpha <> psi, since
## A(U;E,xi,alpha,psi) = 0 unless psi o alpha = psi (Lemma A.2).  Here psi is
## fixed first and only the alpha that stabilise it are visited, which also makes
## |K(U,L)^H| independent of alpha, so it is computed once per character vector
## instead of once per pair (alpha,psi).
##
## The functions of this section are used by cf_gnu_phi_1 and cf_gnu_phi_2 of
## Section 6 and by cf_ss_gnu_phi_1 and cf_ss_gnu_phi_2 of Section 8; the
## restricted counts have psi = 1 throughout, which is expressed by giving the
## character lambda_i only the two values 0 and 1 (the field NL of the context
## record below).
##

## the six elements of Aut(C_2^2) = Sym_3 as permutations of the involutions,
## with the class al of Table 3 and the fixed involution kk (0 if there is none)
cf_perms6 := [ [1,2,3], [2,1,3], [3,2,1], [1,3,2], [2,3,1], [3,1,2] ];;
cf_permAl := [ 0, 1, 1, 1, 2, 2 ];;
cf_permKk := [ 1, 3, 2, 1, 0, 0 ];;

#####################################################
## input: projection tuple prof, the columns R with Theta(U) <> 1, the number nq
##        of primes q | nu_0 and the number m of columns
## output: [has0, chs], the class data of Lemma A.1 contributed by the columns
##         outside R, whose character is 0
##
cf_lamInit := function(prof, R, nq, m)
local has0, chs, inR, i, k;
   has0 := ListWithIdenticalEntries(nq, false);
   chs  := List([1..nq], k-> []);
   inR  := BlistList([1..m], R);
   for i in [1..m] do
      if inR[i] then continue; fi;
      for k in [1..nq] do
         if prof[i].loc[k].d > 0 then has0[k] := true; fi;
      od;
   od;
   return [has0, chs];
end;

#####################################################
## input: projection tuple prof, the columns R, the number nq of primes q
## output: R, ordered so that the columns that create classes at many primes
##         come first; this only changes the order of the search, not its result,
##         but it makes the bound of Lemma A.1 bite earlier
##
cf_lamOrder := function(prof, R, nq)
local ord, sc, i, k, s;
   ord := ShallowCopy(R);
   sc  := [];
   for i in R do
      s := 0;
      for k in [1..nq] do
         if prof[i].loc[k].dm > 0 then s := s + 1; fi;
      od;
      sc[i] := s;
   od;
   Sort(ord, function(a, b) return sc[a] > sc[b]; end);
   return ord;
end;

#####################################################
## input: the depth t and the context record c of cf_lamRec1/cf_lamRec2
## output: true if the character c.lams[i] can be given to the column i = c.ord[t]
##         without violating Lemma A.1; the class data c.has0, c.chs are updated
##         and the previous values are saved in c.ohs[t], c.ols[t]
##
## The caller undoes the update with cf_lamUndo after the recursive call.
##
cf_lamPush := function(t, c, i, lam)
local prof, typs, has0, chs, oh, ol, k, u, nch;
   prof := c.prof;  typs := c.typs;  has0 := c.has0;  chs := c.chs;
   oh   := c.ohs[t]; ol := c.ols[t];
   c.kmax[t] := 0;
   for k in [1..c.nq] do
      oh[k] := has0[k];  ol[k] := Length(chs[k]);  c.kmax[t] := k;
      u := prof[i].loc[k];
      if lam = 0 then
         if u.d > 0 then has0[k] := true; fi;
      else
         if u.dp > 0 then has0[k] := true; fi;
         if u.dm > 0 and not lam in chs[k] then Add(chs[k], lam); fi;
      fi;
      nch := Length(chs[k]);  if has0[k] then nch := nch + 1; fi;
      if nch > 2 or (nch = 2 and not typs[k] = 3) then return false; fi;
   od;
   return true;
end;

cf_lamUndo := function(t, c)
local has0, chs, oh, ol, k;
   has0 := c.has0;  chs := c.chs;  oh := c.ohs[t];  ol := c.ols[t];
   for k in [1..c.kmax[t]] do
      has0[k] := oh[k];
      while Length(chs[k]) > ol[k] do Remove(chs[k]); od;
   od;
end;

#####################################################
## the backtracking for t = 1, Proposition 4.7: at a full character vector the
## summand is A(U;xi,psi) |K(U,L)^H| / |Theta(U)|, with A of Lemma 4.8 and the
## correction -1 for psi = 1
##
cf_lamRec1 := function(t, c)
local i, lam, w, A, allz, m, prof;
   if t > Length(c.ord) then
      w := cf_KUL(c.prof, c.typs, c.tabs, c.lams, c.bs);
      if w = 0 then return; fi;
      m := c.m;  prof := c.prof;  A := 1;  allz := true;
      for i in [1..m] do
         A := A * cf_Atab(prof[i].typ, c.vx[i], c.vp[i]);
         if not c.vp[i] = 0 then allz := false; fi;
      od;
      if allz then A := A - 1; fi;                     # - Delta_{psi=1}
      if not A = 0 then
         c.acc[1] := c.acc[1] + c.mult * A * w / 2^c.r;
      fi;
      return;
   fi;
   i := c.ord[t];
   for lam in [0..c.NL-1] do                          # NL = 4, or 2 if psi = 1
      if cf_lamPush(t, c, i, lam) then
         c.lams[i] := lam;
         c.vx[i]   := lam mod 2;
         c.vp[i]   := QuoInt(lam, 2);
         cf_lamRec1(t+1, c);
      fi;
      cf_lamUndo(t, c);
   od;
   c.lams[i] := 0;  c.vx[i] := 0;  c.vp[i] := 0;
end;

#####################################################
## the backtracking for t = 2, Proposition 4.10: at a full character vector
## |K(U,L)^H| is computed once, and then A(U;E,xi,alpha,psi) of Lemma A.2 for
## every E in c.Es and every alpha in Aut(E) with psi o alpha = psi.
##
## The two isomorphism types E = C_4 and E = C_2^2 need separate searches when
## psi may be nontrivial, because their characters have different ranges (NL = 4
## and NL = 8).  When psi = 1, as in Section 8, the range is NL = 2 for both, the
## search tree is the same, and the two types are handled at the same leaf.
##
cf_lamRec2 := function(t, c)
local i, j, lam, w, h, m, pidx, pi3, PS, al, den;
   if t > Length(c.ord) then
      w := cf_KUL(c.prof, c.typs, c.tabs, c.lams, c.bs);
      if w = 0 then return; fi;
      m := c.m;
      for j in [1..Length(c.Es)] do                     # E = Sylow 2-subgroup
         den := 2^c.r * c.nals[j];                      # |Theta(U)| |Aut(E)|
         if c.Es[j] = "C4" then
            for al in [0,1] do                          # alpha in Aut(C_4)
               h := cf_h("C4", c.tt, c.vx, al, 0, [c.P1]);
               if not h = 0 then
                  c.acc[1] := c.acc[1] + c.mult * h * w / den;
               fi;
            od;
         else
            for i in [1..m] do c.P3[i] := (c.P1[i] + c.P2[i]) mod 2; od;
            PS := c.PS;
            for pidx in [1..6] do                       # alpha in Aut(C_2^2)
               pi3 := cf_perms6[pidx];
               if PS[pi3[1]] = PS[1] and PS[pi3[2]] = PS[2] and PS[pi3[3]] = PS[3]
               then
                  h := cf_h("V4", c.tt, c.vx, cf_permAl[pidx], cf_permKk[pidx], PS);
                  if not h = 0 then
                     c.acc[1] := c.acc[1] + c.mult * h * w / den;
                  fi;
               fi;
            od;
         fi;
      od;
      return;
   fi;
   i := c.ord[t];
   for lam in [0..c.NL-1] do                          # NL = 4, 8, or 2 if psi = 1
      if cf_lamPush(t, c, i, lam) then
         c.lams[i] := lam;
         c.vx[i]   := lam mod 2;
         c.P1[i]   := QuoInt(lam, 2) mod 2;
         c.P2[i]   := QuoInt(lam, 4) mod 2;
         cf_lamRec2(t+1, c);
      fi;
      cf_lamUndo(t, c);
   od;
   c.lams[i] := 0;  c.vx[i] := 0;  c.P1[i] := 0;  c.P2[i] := 0;
end;

#####################################################
## the scratch space that cf_lamRec1/cf_lamRec2 walk on; allocated once per
## projection tuple rather than once per node of the search.  The caller adds
##
##   has0, chs   the class data of cf_lamInit
##   mult        the multiplicity of the projection tuple
##   NL          the number of admissible characters per column: 4 for t = 1,
##               4 resp. 8 for t = 2 with E = C_4 resp. E = C_2^2, and 2 if psi
##               is forced to be trivial, as in Section 8
##   vp          (t = 1) the 0/1 vector of psi
##   tt, Es, nals, P1, P2, P3, PS   (t = 2) the tables of cf_Ttab, the list of
##               isomorphism types E to be handled at a leaf together with their
##               |Aut(E)|, and the scratch vectors for psi as in cf_h
##
## and reads the result off acc[1] when the search is done.
##
cf_lamCtx := function(prof, typs, tabs, bs, R, nq, m, r)
local c;
   c := rec( prof := prof, typs := typs, tabs := tabs, bs := bs,
             nq := nq, m := m, r := r,
             ord  := cf_lamOrder(prof, R, nq),
             lams := ListWithIdenticalEntries(m, 0),
             vx   := ListWithIdenticalEntries(m, 0),
             ohs  := List([1..r+1], x-> ListWithIdenticalEntries(nq, false)),
             ols  := List([1..r+1], x-> ListWithIdenticalEntries(nq, 0)),
             kmax := ListWithIdenticalEntries(r+1, 0),
             acc  := [0] );
   return c;
end;

######################################################
##
## 6.  The three cases of gnu_Phi(n,l):  Corollary 3.11, Propositions 4.7 and 4.10
##
## In all three functions n is cubefree, l | n, and nu = n/l = 2^t nu_0 with nu_0
## odd; the caller has checked that t = v_2(nu) is 0, 1 or 2, respectively.  The
## outer two sums are the same everywhere: L runs over A(nu) resp. A(nu_0), and
## U = (U_1,...,U_m) over the projection tuples in the product of the U(p_i,e_i,L)
## for the columns (p_i,e_i) of l.  The tuples are built from the collapsed sets
## cf_Udata(p,e,L), so a tuple stands for mult of them, and Theta(U) is the
## elementary abelian 2-group with basis the columns of type (4) or (5), listed
## in R; an element of Theta(U) is a 0/1 vector over the columns supported on R.
##

#####################################################
## input: cubefree n and a divisor l of n with v_2(n/l) = 0
## output: gnu_Phi(n,l), by Corollary 3.11
##
cf_gnu_phi_0 := function(n, l)
local nu, cols, tot, L, Us, tabs, typs, nq, tup, prof, mult, m, R, r, msk, vx,
      prod, k, bs, it, i;
   nu  := n/l;
   if l = 1 then cols := []; else cols := cf_facs(l); fi;
   tot := 0;
   for L in cf_A(nu) do                                     # L in A(nu)
      if not cf_feasible(cols, L) then continue; fi;
      Us   := List(cols, x-> cf_Udata(x[1], x[2], L));
      nq   := Length(L.primes);
      tabs := List(L.primes, cf_tab);
      typs := List(L.sylow, x-> Position([[1,1],[2,1],[2,2]], x));
      m    := Length(cols);
      prof := EmptyPlist(m);                                # reused for every tuple
      it   := IteratorOfCartesianProduct(Us);               # avoids building the
      while not IsDoneIterator(it) do                       # full list of tuples
         tup  := NextIterator(it);                          # U = projection tuple
         mult := 1;
         for i in [1..m] do prof[i] := tup[i][1]; mult := mult * tup[i][2]; od;
         R    := Filtered([1..m], i-> prof[i].theta = 2);
         r    := Length(R);
         bs := List([1..nq], k-> cf_KqtBase(typs[k], tabs[k], prof, k));
         vx := ListWithIdenticalEntries(m, 0);              # reused for every theta
         for msk in [0..2^r-1] do                           # theta in Theta(U)
            for k in [1..r] do vx[R[k]] := QuoInt(msk, 2^(k-1)) mod 2; od;
            prod := 1;
            for k in [1..nq] do                              # q | nu
               prod := prod * cf_KqtB(typs[k], tabs[k], prof, vx, k, bs[k]);
               if prod = 0 then break; fi;
            od;
            if not prod = 0 then
               tot := tot + mult * prod / 2^r;               # 1/|Theta(U)|
            fi;
         od;
      od;
   od;
   return tot;
end;

#####################################################
## input: cubefree n and a divisor l of n with v_2(n/l) = 1
## output: gnu_Phi(n,l), by Proposition 4.7
##
## The pairs (xi,psi) are enumerated as character vectors by cf_lamRec1, see
## Section 5; cf_gnu_phi_1_OLD of Section 10 evaluates the same sum directly.
##
cf_gnu_phi_1 := function(n, l)
local nu0, cols, tot, L, Us, tabs, typs, nq, tup, prof, mult, m, R, r, it, i,
      bs, st, c;
   nu0 := n/(2*l);
   if l = 1 then cols := []; else cols := cf_facs(l); fi;
   tot := 0;
   for L in cf_A(nu0) do                                    # L in A(nu_0)
      if not cf_feasible(cols, L) then continue; fi;
      Us   := List(cols, x-> cf_Udata(x[1], x[2], L));
      tabs := List(L.primes, cf_tab);
      typs := List(L.sylow, x-> Position([[1,1],[2,1],[2,2]], x));
      nq   := Length(typs);
      m    := Length(cols);
      prof := EmptyPlist(m);
      it   := IteratorOfCartesianProduct(Us);
      while not IsDoneIterator(it) do
         tup  := NextIterator(it);                          # U = projection tuple
         mult := 1;
         for i in [1..m] do prof[i] := tup[i][1]; mult := mult * tup[i][2]; od;
         R    := Filtered([1..m], i-> prof[i].theta = 2);
         r    := Length(R);
         bs   := List([1..nq], k-> cf_KqtBase(typs[k], tabs[k], prof, k));
         st   := cf_lamInit(prof, R, nq, m);
         c    := cf_lamCtx(prof, typs, tabs, bs, R, nq, m, r);
         c.has0 := st[1];  c.chs := st[2];
         c.vp   := ListWithIdenticalEntries(m, 0);
         c.mult := mult;   c.NL := 4;                       # lambda = xi + 2 psi
         cf_lamRec1(1, c);
         tot := tot + c.acc[1];
      od;
   od;
   return tot;
end;

#####################################################
## input: cubefree n and a divisor l of n with v_2(n/l) = 2
## output: gnu_Phi(n,l), by Proposition 4.10
##
## The two isomorphism types E = C_4 and E = C_2^2 are treated in turn.  A
## homomorphism psi in Hom(E,Theta(U)) is given by the images of the involutions
## of E, each a 0/1 vector over the columns supported on R; for E = C_4 this is
## the single vector psi(x) for a generator x of E, and for E = C_2^2 the third
## image is the sum of the other two.  The triples (xi,alpha,psi) are enumerated
## as character vectors by cf_lamRec2, see Section 5; cf_gnu_phi_2_OLD of
## Section 10 evaluates the same sum directly.
##
cf_gnu_phi_2 := function(n, l)
local nu0, cols, tot, L, Us, tabs, typs, nq, tup, prof, mult, m, R, r, it, i,
      bs, tt, st, c, E;
   nu0 := n/(4*l);
   if l = 1 then cols := []; else cols := cf_facs(l); fi;
   tot := 0;
   for L in cf_A(nu0) do                                    # L in A(nu_0)
      if not cf_feasible(cols, L) then continue; fi;
      Us   := List(cols, x-> cf_Udata(x[1], x[2], L));
      tabs := List(L.primes, cf_tab);
      typs := List(L.sylow, x-> Position([[1,1],[2,1],[2,2]], x));
      nq   := Length(typs);
      m    := Length(cols);
      prof := EmptyPlist(m);
      it   := IteratorOfCartesianProduct(Us);
      while not IsDoneIterator(it) do
         tup  := NextIterator(it);                          # U = projection tuple
         mult := 1;
         for i in [1..m] do prof[i] := tup[i][1]; mult := mult * tup[i][2]; od;
         R    := Filtered([1..m], i-> prof[i].theta = 2);
         r    := Length(R);
         bs   := List([1..nq], k-> cf_KqtBase(typs[k], tabs[k], prof, k));
         tt   := List(prof, cf_Ttab);
         for E in [ "C4", "V4" ] do                         # E = Sylow 2-subgroup
            st := cf_lamInit(prof, R, nq, m);
            c  := cf_lamCtx(prof, typs, tabs, bs, R, nq, m, r);
            c.has0 := st[1];  c.chs := st[2];
            c.tt   := tt;     c.mult := mult;   c.Es := [E];
            c.P1   := ListWithIdenticalEntries(m, 0);
            c.P2   := ListWithIdenticalEntries(m, 0);
            c.P3   := ListWithIdenticalEntries(m, 0);
            c.PS   := [ c.P1, c.P2, c.P3 ];
            if E = "C4" then c.nals := [2];  c.NL := 4;   # lambda = xi + 2 psi^1
                        else c.nals := [6];  c.NL := 8; fi;
            cf_lamRec2(1, c);
            tot := tot + c.acc[1];
         od;
      od;
   od;
   return tot;
end;


######################################################
##
## 7.  The main function:  Theorem 4.11
##

#####################################################
## input: a cubefree integer n >= 1 whose graph Gamma(n) is connected
## output: gnu(n), evaluated by the sums of Theorem 4.11
##
cf_gnu_connected := function(n)
local tot, s, d, l, t;
   tot := 0;
   for s in cf_S(n) do                                  # s = order of the simple factor
      for d in DivisorsInt(cf_Q(n/s)) do                # d = order of the Frattini subgroup
         for l in DivisorsInt(n/(s*d)) do               # l = order of the socle
            t := cf_vq(n/(s*d*l), 2);
            if   t = 0 then tot := tot + cf_gnu_phi_0(n/(s*d), l);
            elif t = 1 then tot := tot + cf_gnu_phi_1(n/(s*d), l);
            else            tot := tot + cf_gnu_phi_2(n/(s*d), l);
            fi;
         od;
      od;
   od;
   return tot;
end;

#####################################################
## input: a cubefree integer n >= 1
## output: gnu(n), the number of isomorphism types of groups of order n
##
## By Remark 3.16, every group of order n is the direct product of its Hall
## C-subgroups, where C runs over the connected components of Gamma(n); so gnu is
## multiplicative over the n_C returned by cf_components. For a connected Gamma(n)
## (in particular for every even n) this is just one call of cf_gnu_connected.
##
NumberCubefreeGroups := function(n)
   if not IsPosInt(n) then Error("NumberCubefreeGroups: <n> must be a positive integer"); fi;
   if ForAny(Collected(FactorsInt(n)), x-> x[2] > 2) then
      Error("NumberCubefreeGroups: <n> must be cubefree");
   fi;
   if n = 1 then return 1; fi;
   return Product(cf_components(n), cf_gnu_connected);
end;


######################################################
##
## 8.  Restricted counts: solvable and supersolvable groups, see Remark 4.14
##
##    NumberCubefreeSolvableGroups(n)        gnu_solv(n)
##    NumberCubefreeSupersolvableGroups(n)   gnu_ssolv(n)
##
## Both are obtained by restricting the objects that the sums of Theorem 4.11 run
## over.  Both counts are still multiplicative over the components of Gamma(n):
## a group is solvable resp. supersolvable if and only if all of its Hall
## C-subgroups are.
##
## Solvable: every cubefree group is G = A x L with A trivial or simple and L
## solvable, so gnu_solv(n) is the summand for s = 1 of the outer sum.  Nothing
## else changes, so cf_solv_gnu_connected calls cf_gnu_phi_0/1/2 of Section 6
## unchanged.
##
## Supersolvable: the functions below are copies of those in Sections 2, 4 and 6
## with the restrictions (i)-(iii) described next built in, so that Sections 1-7
## remain untouched.  The character enumeration of Section 5 is reused unchanged,
## with the characters restricted to lambda_i in {0,1} because psi = 1, see (ii).
##
## Recall that G is supersolvable if and only if G is solvable and every
## projection K_i <= GL_{e_i}(p_i) with e_i = 2 of the socle complement K of
## G/Phi(G) is reducible.  Write K_i = E_i U_i, where U_i = pi_i(O) is the
## projection of the odd part O of K and E_i = pi_i(E) is the projection of the
## Sylow 2-subgroup E of K.  In the notation of Definition 4.6 the condition on
## the columns with e_i = 2 is that none of the following occurs:
##
##   (i)   a column of type (5):  here U_i is irreducible;
##   (ii)  a column of type (4) with epsilon(E)_i <> 1:  here U_i is diagonal, but
##         E_i swaps the two eigenspaces of U_i, so K_i is monomial irreducible;
##   (iii) a column of type (2) whose E_i is an irreducible cyclic group of order
##         4:  this needs t = 2 and 4 not dividing p_i - 1, that is, delta = 0.
##
## The columns of types (1) and (3), and those of type (4) with epsilon(E)_i = 1,
## always give K_i <= D(p_i).  Accordingly:
##
##   (i)   removes the irreducible groups Sigma(p,b) from U(p,2,L), see
##         cf_ss_Upel;
##   (ii)  forces the summation index psi of Propositions 4.7 and 4.10 to be
##         trivial at the columns of type (4); after (i) the group Theta(U) is
##         generated by the columns of type (4), so this just means psi = 1, see
##         cf_ss_gnu_phi_1 and cf_ss_gnu_phi_2;
##   (iii) removes one class from the number rho(C_4,alpha) of Table 3 when
##         delta = 0, see cf_ss_rho.  For t = 1 this condition is vacuous, since
##         every involution of GL_2(p) is diagonalisable, so cf_Atab is reused
##         unchanged; for t = 0 there is no E at all.
##
## All three conditions are invariant under conjugation by N(U), so the Burnside
## averages over Theta(U) in Corollary 3.11 and Propositions 4.7 and 4.10 are
## taken over the restricted sets exactly as before.
##

#####################################################
## input: a cubefree integer n >= 1 whose graph Gamma(n) is connected
## output: gnu_solv(n), the summand for s = 1 of Theorem 4.11
##
cf_solv_gnu_connected := function(n)
local tot, d, l, t;
   tot := 0;
   for d in DivisorsInt(cf_Q(n)) do                  # d = order of the Frattini subgroup
      for l in DivisorsInt(n/d) do                   # l = order of the socle
         t := cf_vq(n/(d*l), 2);
         if   t = 0 then tot := tot + cf_gnu_phi_0(n/d, l);
         elif t = 1 then tot := tot + cf_gnu_phi_1(n/d, l);
         else            tot := tot + cf_gnu_phi_2(n/d, l);
         fi;
      od;
   od;
   return tot;
end;

#####################################################
## input: a cubefree integer n >= 1
## output: gnu_solv(n), the number of solvable groups of order n
##
NumberCubefreeSolvableGroups := function(n)
   if not IsPosInt(n) then
      Error("NumberCubefreeSolvableGroups: <n> must be a positive integer");
   fi;
   if ForAny(Collected(FactorsInt(n)), x-> x[2] > 2) then
      Error("NumberCubefreeSolvableGroups: <n> must be cubefree");
   fi;
   if n = 1 then return 1; fi;
   return Product(cf_components(n), cf_solv_gnu_connected);
end;


#####################################################
## input: prime p, e in {1,2}, abelian group record L
## output: the reducible groups of U(p,e,L), that is, condition (i) applied to
##         cf_Upel: for e = 2 only the columns of types (2), (3) and (4) are kept
##
cf_ss_Upel := function(p, e, L)
local nq, res, opts, bs, tup, sw, th, loc, k, ee, sc, delta, typ;
   nq := Length(L.primes);  res := [];
   delta := 0;  if not p = 2 and (p-1) mod 4 = 0 then delta := 1; fi;

   ## e = 1: unchanged, every column of type (1) (or (0) if p = 2) is reducible
   if e = 1 then
      if p = 2 then typ := 0; else typ := 1; fi;
      opts := List([1..nq], k-> [0..Minimum(cf_largestCyclicQuot(L.sylow[k]),
                                            cf_vq(p-1,L.primes[k]))]);
      for tup in Cartesian(opts) do
         loc := List([1..nq], k-> rec(j:=tup[k], d:=Minimum(tup[k],1),
                                      dp:=Minimum(tup[k],1), dm:=0));
         Add(res, rec(theta:=1, typ:=typ, delta:=delta, loc:=loc));
      od;
      return res;
   fi;

   ## e = 2, reducible: as in cf_Upel, one subgroup from each swap orbit on the
   ## subgroups of D(p); the irreducible U = Sigma(p,b) of type (5) are dropped
   bs   := List([1..nq], k-> cf_vq(p-1,L.primes[k]));
   opts := List([1..nq], k-> cf_Dsubgroups(L.primes[k], bs[k], L.sylow[k]));
   for tup in Cartesian(opts) do
      sw := List([1..nq], k-> cf_swapSub(tup[k], L.primes[k], bs[k]));
      if List(sw,u->u.gens) < List(tup,u->u.gens) then continue; fi;
      sc := ForAll(tup, cf_isScalar);
      if List(sw,u->u.gens) = List(tup,u->u.gens) and not sc
         then th := 2; else th := 1; fi;
      if sc then typ := 2; elif th = 2 then typ := 4; else typ := 3; fi;
      loc := [];
      for k in [1..nq] do
         if th = 2 then ee := cf_eigen(tup[k], L.primes[k], bs[k]);
                   else ee := [tup[k].d, 0]; fi;
         Add(loc, rec(j:=tup[k].j, d:=tup[k].d, dp:=ee[1], dm:=ee[2]));
      od;
      Add(res, rec(theta:=th, typ:=typ, delta:=delta, loc:=loc));
   od;

   return res;
end;

#####################################################
## the cache for the restricted sets, and the function to empty it; both work
## exactly as cf_Udata and cf_clearcache, but with their own dictionary
##
cf_ss_cache := NewDictionary([1,1], true);;

cf_ss_Udata := function(p, e, L)
local val, key, k;
   key := [p, e];
   for k in [1..Length(L.primes)] do
      Add(key, L.primes[k]);
      Add(key, 2*L.sylow[k][1] + L.sylow[k][2]);
   od;
   val := LookupDictionary(cf_ss_cache, key);
   if not val = fail then return val; fi;
   val := Collected(cf_ss_Upel(p, e, L));
   AddDictionary(cf_ss_cache, key, val);
   return val;
end;

cf_ss_clearcache := function()
   cf_ss_cache := NewDictionary([1,1], true);
   return;
end;

#####################################################
## input: as cf_rho
## output: rho(P,alpha) with the class of the irreducible 2-dimensional
##         representation of C_4 removed, that is, condition (iii)
##
## If delta = 0, then exactly one of the rho(C_4,alpha) classes maps C_4 onto the
## irreducible group Sigma(p,4); if delta = 1, then no 2-dimensional
## representation of C_4 is irreducible and nothing changes.  For P = "C2" and
## P = "V4" all representations are diagonalisable, hence reducible.
##
cf_ss_rho := function(P, al, delta)
   if P = "C4" and delta = 0 then return cf_rho(P, al, delta) - 1; fi;
   return cf_rho(P, al, delta);
end;

#####################################################
## input, output: as cf_T, with cf_ss_rho in place of cf_rho at the columns of
##                type (2)
##
cf_ss_T := function(u, P, xi, al, pnz)
   if pnz = 1 then
      if u.typ < 4 then return 0; fi;
      if P = "C2" then return 1; else return 2; fi;   # |Hom(ker psi, C_{2^a})|
   fi;
   if P = "1" or u.typ = 0 then return 1; fi;
   if u.typ = 1 then return cf_phia(P, al, u.delta); fi;
   if u.typ = 2 then return cf_ss_rho(P, al, u.delta); fi;
   if u.typ = 3 then return cf_phia(P, al, u.delta)^2; fi;
   if u.typ = 4 then
      if xi = 0 then return cf_phia(P, al, u.delta)^2; fi;
      return cf_phia(P, cf_alsq(P,al), u.delta);
   fi;
   if xi = 0 or u.delta = 1 then return cf_phic(P, al); fi;
   return cf_phim(P, al);
end;

#####################################################
## input, output: as cf_Ttab, but built from cf_ss_T and stored in u.sstab, so
##                that the two tables of a column can coexist
##
cf_ss_Ttab := function(u)
local xi, pn, t;
   if IsBound(u.sstab) then return u.sstab; fi;
   t := [];
   for xi in [0,1] do
      t[xi+1] := [];
      for pn in [0,1] do
         t[xi+1][pn+1] := [ cf_ss_T(u, "C2", xi, 0, pn),
                            cf_ss_T(u, "C4", xi, 0, pn), cf_ss_T(u, "C4", xi, 1, pn),
                            cf_ss_T(u, "V4", xi, 0, pn), cf_ss_T(u, "V4", xi, 1, pn),
                            cf_ss_T(u, "V4", xi, 2, pn) ];
      od;
   od;
   u.sstab := t;
   return t;
end;

#####################################################
## input: cubefree n and a divisor l of n with v_2(n/l) = 0
## output: the supersolvable part of gnu_Phi(n,l); this is cf_gnu_phi_0 evaluated
##         over the restricted projection tuples of cf_ss_Udata
##
cf_ss_gnu_phi_0 := function(n, l)
local nu, cols, tot, L, Us, tabs, typs, nq, tup, prof, mult, m, R, r, msk, vx,
      prod, k, bs, it, i;
   nu  := n/l;
   if l = 1 then cols := []; else cols := cf_facs(l); fi;
   tot := 0;
   for L in cf_A(nu) do                                     # L in A(nu)
      if not cf_feasible(cols, L) then continue; fi;
      Us   := List(cols, x-> cf_ss_Udata(x[1], x[2], L));    # only reducible U
      nq   := Length(L.primes);
      tabs := List(L.primes, cf_tab);
      typs := List(L.sylow, x-> Position([[1,1],[2,1],[2,2]], x));
      m    := Length(cols);
      prof := EmptyPlist(m);
      it   := IteratorOfCartesianProduct(Us);
      while not IsDoneIterator(it) do
         tup  := NextIterator(it);
         mult := 1;
         for i in [1..m] do prof[i] := tup[i][1]; mult := mult * tup[i][2]; od;
         R    := Filtered([1..m], i-> prof[i].theta = 2);
         r    := Length(R);
         bs := List([1..nq], k-> cf_KqtBase(typs[k], tabs[k], prof, k));
         vx := ListWithIdenticalEntries(m, 0);
         for msk in [0..2^r-1] do                           # theta in Theta(U)
            for k in [1..r] do vx[R[k]] := QuoInt(msk, 2^(k-1)) mod 2; od;
            prod := 1;
            for k in [1..nq] do                             # q | nu
               prod := prod * cf_KqtB(typs[k], tabs[k], prof, vx, k, bs[k]);
               if prod = 0 then break; fi;
            od;
            if not prod = 0 then
               tot := tot + mult * prod / 2^r;              # 1/|Theta(U)|
            fi;
         od;
      od;
   od;
   return tot;
end;

#####################################################
## input: cubefree n and a divisor l of n with v_2(n/l) = 1
## output: the supersolvable part of gnu_Phi(n,l); this is cf_gnu_phi_1 over the
##         restricted tuples and with psi = 1, so the sum over psi disappears
##
cf_ss_gnu_phi_1 := function(n, l)
local nu0, cols, tot, L, Us, tabs, typs, nq, tup, prof, mult, m, R, r, it, i,
      bs, st, c;
   nu0 := n/(2*l);
   if l = 1 then cols := []; else cols := cf_facs(l); fi;
   tot := 0;
   for L in cf_A(nu0) do                                    # L in A(nu_0)
      if not cf_feasible(cols, L) then continue; fi;
      Us   := List(cols, x-> cf_ss_Udata(x[1], x[2], L));    # only reducible U
      tabs := List(L.primes, cf_tab);
      typs := List(L.sylow, x-> Position([[1,1],[2,1],[2,2]], x));
      nq   := Length(typs);
      m    := Length(cols);
      prof := EmptyPlist(m);
      it   := IteratorOfCartesianProduct(Us);
      while not IsDoneIterator(it) do
         tup  := NextIterator(it);                          # U = projection tuple
         mult := 1;
         for i in [1..m] do prof[i] := tup[i][1]; mult := mult * tup[i][2]; od;
         R    := Filtered([1..m], i-> prof[i].theta = 2);
         r    := Length(R);
         bs   := List([1..nq], k-> cf_KqtBase(typs[k], tabs[k], prof, k));
         st   := cf_lamInit(prof, R, nq, m);
         c    := cf_lamCtx(prof, typs, tabs, bs, R, nq, m, r);
         c.has0 := st[1];  c.chs := st[2];
         c.vp   := ListWithIdenticalEntries(m, 0);          # psi = 1 throughout
         c.mult := mult;   c.NL := 2;                       # lambda = xi
         cf_lamRec1(1, c);
         tot := tot + c.acc[1];
      od;
   od;
   return tot;
end;

#####################################################
## input: cubefree n and a divisor l of n with v_2(n/l) = 2
## output: the supersolvable part of gnu_Phi(n,l); this is cf_gnu_phi_2 over the
##         restricted tuples, with psi = 1 (so the sums over psi disappear) and
##         with the tables cf_ss_Ttab, which impose condition (iii)
##
cf_ss_gnu_phi_2 := function(n, l)
local nu0, cols, tot, L, Us, tabs, typs, nq, tup, prof, mult, m, R, r, it, i,
      bs, tt, st, c;
   nu0 := n/(4*l);
   if l = 1 then cols := []; else cols := cf_facs(l); fi;
   tot := 0;
   for L in cf_A(nu0) do                                    # L in A(nu_0)
      if not cf_feasible(cols, L) then continue; fi;
      Us   := List(cols, x-> cf_ss_Udata(x[1], x[2], L));    # only reducible U
      tabs := List(L.primes, cf_tab);
      typs := List(L.sylow, x-> Position([[1,1],[2,1],[2,2]], x));
      nq   := Length(typs);
      m    := Length(cols);
      prof := EmptyPlist(m);
      it   := IteratorOfCartesianProduct(Us);
      while not IsDoneIterator(it) do
         tup  := NextIterator(it);                          # U = projection tuple
         mult := 1;
         for i in [1..m] do prof[i] := tup[i][1]; mult := mult * tup[i][2]; od;
         R    := Filtered([1..m], i-> prof[i].theta = 2);
         r    := Length(R);
         bs   := List([1..nq], k-> cf_KqtBase(typs[k], tabs[k], prof, k));
         tt   := List(prof, cf_ss_Ttab);                    # tables for cf_h
         st   := cf_lamInit(prof, R, nq, m);
         c    := cf_lamCtx(prof, typs, tabs, bs, R, nq, m, r);
         c.has0 := st[1];  c.chs := st[2];
         c.tt   := tt;     c.mult := mult;
         c.Es   := [ "C4", "V4" ];   c.nals := [2, 6];      # E = Sylow 2-subgroup
         c.P1   := ListWithIdenticalEntries(m, 0);          # psi = 1 throughout
         c.P2   := ListWithIdenticalEntries(m, 0);
         c.P3   := ListWithIdenticalEntries(m, 0);
         c.PS   := [ c.P1, c.P2, c.P3 ];
         c.NL   := 2;                                       # lambda = xi
         cf_lamRec2(1, c);
         tot := tot + c.acc[1];
      od;
   od;
   return tot;
end;

#####################################################
## input: a cubefree integer n >= 1 whose graph Gamma(n) is connected
## output: gnu_ssolv(n), evaluated by the restricted sums of Theorem 4.11
##
cf_ss_gnu_connected := function(n)
local tot, d, l, t;
   tot := 0;
   for d in DivisorsInt(cf_Q(n)) do                  # d = order of the Frattini subgroup
      for l in DivisorsInt(n/d) do                   # l = order of the socle
         t := cf_vq(n/(d*l), 2);
         if   t = 0 then tot := tot + cf_ss_gnu_phi_0(n/d, l);
         elif t = 1 then tot := tot + cf_ss_gnu_phi_1(n/d, l);
         else            tot := tot + cf_ss_gnu_phi_2(n/d, l);
         fi;
      od;
   od;
   return tot;
end;

#####################################################
## input: a cubefree integer n >= 1
## output: gnu_ssolv(n), the number of supersolvable groups of order n
##
NumberCubefreeSupersolvableGroups := function(n)
   if not IsPosInt(n) then
      Error("NumberCubefreeSupersolvableGroups: <n> must be a positive integer");
   fi;
   if ForAny(Collected(FactorsInt(n)), x-> x[2] > 2) then
      Error("NumberCubefreeSupersolvableGroups: <n> must be cubefree");
   fi;
   if n = 1 then return 1; fi;
   return Product(cf_components(n), cf_ss_gnu_connected);
end;


######################################################
##
## 9.  Restricted count: groups with cyclic Sylow subgroups
##
##    NumberCubefreeCGroups(n)   gnu_cyc(n)
##
## A group all of whose Sylow subgroups are cyclic is a C-group (also called a
## Z-group); by Hoelder, Burnside and Zassenhaus such a group is metacyclic, in
## particular solvable.  As in Section 8 the count is obtained by restricting the
## objects that the sums of Theorem 4.11 run over, so that Sections 1-8 remain
## untouched.  It is again multiplicative over the components of Gamma(n), since
## a direct product of groups of coprime orders is a C-group if and only if all
## of its factors are.
##
## Let G be a group of cubefree order n = s*d*l*nu counted by the term (s,d,l,L)
## of Theorem 4.11: s = |A| for the simple direct factor A of G, d = |Phi(G)|,
## l = |Soc(G/Phi(G))| and nu = |K| for the socle complement K of G/Phi(G), whose
## Sylow 2-subgroup is E of order 2^t and whose odd part is isomorphic to L.
## Then G is a C-group if and only if
##
##   (a) s = 1;
##   (b) l is squarefree;
##   (c) gcd(l,nu) = 1;
##   (d) every Sylow subgroup of K is cyclic, that is, L has no Sylow subgroup of
##       rank 2, and E is not C_2 x C_2.
##
## For the necessity: (a) the cubefree simple groups of cf_S are the PSL(2,p) with
## 4 || |PSL(2,p)|, and their Sylow 2-subgroups are dihedral, hence C_2 x C_2;
## (b) if p^2 | l then Soc(G/Phi(G)) contains C_p x C_p; (c) if p | l and p | nu
## then e_i = 1 for the column of p by (b), so the Sylow p-subgroup K_p of K has
## trivial image in Aut(Soc_p) = GL_1(p) = C_{p-1}, and the Sylow p-subgroup of G
## is Soc_p x K_p = C_p x C_p; (d) if p^2 | nu then p divides neither d nor l by
## (c), so the Sylow p-subgroup of G is the one of K.
##
## For the sufficiency let p^2 | n.  If p | d, then the Sylow p-subgroup of G is
## cyclic for every G counted by the term, and no condition on d is needed: the
## p-part N of Phi(G) is normal in G of order p, and if the Sylow p-subgroup P of
## G were C_p x C_p, then N would have a complement in P and hence, by Gaschuetz's
## theorem, in G, contradicting N <= Phi(G).  If p does not divide d, then p^2
## divides l*nu, so p^2 | nu by (b) and (c), and the Sylow p-subgroup of G is the
## one of K, which is cyclic by (d).
##
## Accordingly:
##
##   (a)   drops the outer sum over s, as in cf_solv_gnu_connected;
##   (b),(c) restrict the divisors l, see cf_c_gnu_connected;
##   (d)   lets L run over cf_c_A(nu) instead of cf_A(nu), and leaves only the
##         summand E = C_4 of Proposition 4.10, see cf_c_gnu_phi_0/1/2.
##
## No further restriction of the sets U(p,e,L) is needed, and no new cache: by (b)
## every column has e_i = 1, so every U in U(p,1,L) has Theta(U) = 1 and column
## type (1), or type (0) for p = 2.  The loops over Theta(U) below are kept as in
## Sections 6 and 8; they simply run over the trivial group.
##

#####################################################
## input: cubefree n
## output: the abelian groups of order n all of whose Sylow subgroups are cyclic,
##         in the format of cf_A; this is the cyclic group of order n only
##
cf_c_A := function(n)
local facs;
   facs := Collected(FactorsInt(n));
   if facs = [[1,1]] then return [ rec(primes:=[], sylow:=[]) ]; fi;   # n = 1
   return [ rec(primes := List(facs, x-> x[1]),
                sylow  := List(facs, x-> [x[2],1])) ];
end;

#####################################################
## input: cubefree n and a squarefree divisor l of n with v_2(n/l) = 0
## output: the C-group part of gnu_Phi(n,l); this is cf_gnu_phi_0 with L
##         restricted to the cyclic group of order nu
##
cf_c_gnu_phi_0 := function(n, l)
local nu, cols, tot, L, Us, tabs, typs, nq, tup, prof, mult, m, R, r, msk, vx,
      prod, k, bs, it, i;
   nu  := n/l;
   if l = 1 then cols := []; else cols := Collected(FactorsInt(l)); fi;
   tot := 0;
   for L in cf_c_A(nu) do                                   # L in A(nu), cyclic
      if not cf_feasible(cols, L) then continue; fi;
      Us   := List(cols, x-> cf_Udata(x[1], x[2], L));
      nq   := Length(L.primes);
      tabs := List(L.primes, cf_tab);
      typs := List(L.sylow, x-> Position([[1,1],[2,1],[2,2]], x));
      m    := Length(cols);
      prof := EmptyPlist(m);
      it   := IteratorOfCartesianProduct(Us);
      while not IsDoneIterator(it) do
         tup  := NextIterator(it);
         mult := 1;
         for i in [1..m] do prof[i] := tup[i][1]; mult := mult * tup[i][2]; od;
         R    := Filtered([1..m], i-> prof[i].theta = 2);
         r    := Length(R);
         bs := List([1..nq], k-> cf_KqtBase(typs[k], tabs[k], prof, k));
         vx := ListWithIdenticalEntries(m, 0);
         for msk in [0..2^r-1] do                           # theta in Theta(U)
            for k in [1..r] do vx[R[k]] := QuoInt(msk, 2^(k-1)) mod 2; od;
            prod := 1;
            for k in [1..nq] do                             # q | nu
               prod := prod * cf_KqtB(typs[k], tabs[k], prof, vx, k, bs[k]);
               if prod = 0 then break; fi;
            od;
            if not prod = 0 then
               tot := tot + mult * prod / 2^r;              # 1/|Theta(U)|
            fi;
         od;
      od;
   od;
   return tot;
end;

#####################################################
## input: cubefree n and a squarefree divisor l of n with v_2(n/l) = 1
## output: the C-group part of gnu_Phi(n,l); this is cf_gnu_phi_1 with L
##         restricted to the cyclic group of order nu_0
##
cf_c_gnu_phi_1 := function(n, l)
local nu0, cols, tot, L, Us, tabs, typs, nq, tup, prof, mult, m, R, r, vx, vp,
      A, h, k, it, i, bs, lms, mx, mp;
   nu0 := n/(2*l);
   if l = 1 then cols := []; else cols := Collected(FactorsInt(l)); fi;
   tot := 0;
   for L in cf_c_A(nu0) do                                  # L in A(nu_0), cyclic
      if not cf_feasible(cols, L) then continue; fi;
      Us   := List(cols, x-> cf_Udata(x[1], x[2], L));
      tabs := List(L.primes, cf_tab);
      typs := List(L.sylow, x-> Position([[1,1],[2,1],[2,2]], x));
      nq   := Length(typs);
      m    := Length(cols);
      prof := EmptyPlist(m);
      it   := IteratorOfCartesianProduct(Us);
      while not IsDoneIterator(it) do
         tup  := NextIterator(it);
         mult := 1;
         for i in [1..m] do prof[i] := tup[i][1]; mult := mult * tup[i][2]; od;
         R    := Filtered([1..m], i-> prof[i].theta = 2);
         r    := Length(R);
         bs   := List([1..nq], k-> cf_KqtBase(typs[k], tabs[k], prof, k));
         vx   := ListWithIdenticalEntries(m, 0);            # reused for every xi
         vp   := ListWithIdenticalEntries(m, 0);            # reused for every psi
         lms  := ListWithIdenticalEntries(m, 0);            # column characters
         for mx in [0..2^r-1] do                            # xi in Theta(U)
            for k in [1..r] do vx[R[k]] := QuoInt(mx, 2^(k-1)) mod 2; od;
            for mp in [0..2^r-1] do                         # psi in Theta(U)
               for k in [1..r] do vp[R[k]] := QuoInt(mp, 2^(k-1)) mod 2; od;
               A := Product([1..m], i-> cf_Atab(prof[i].typ, vx[i], vp[i]));
               if mp = 0 then A := A - 1; fi;               # - Delta_{psi=1}
               if not A = 0 then
                  for i in [1..m] do lms[i] := vx[i] + 2*vp[i]; od;
                  h := cf_KUL(prof, typs, tabs, lms, bs);
                  tot := tot + mult * A * h / 2^r;          # 1/|Theta(U)|
               fi;
            od;
         od;
      od;
   od;
   return tot;
end;

#####################################################
## input: cubefree n and a squarefree divisor l of n with v_2(n/l) = 2
## output: the C-group part of gnu_Phi(n,l); this is cf_gnu_phi_2 with L
##         restricted to the cyclic group of order nu_0 and with E = C_4, since
##         E is the Sylow 2-subgroup of G here (l and d are odd)
##
cf_c_gnu_phi_2 := function(n, l)
local nu0, cols, tot, L, Us, tabs, typs, nq, tup, prof, mult, m, R, r,
      nal, al, vx, P1, h, w, k, it, i, bs, tt, lms, mx, mp;
   nu0 := n/(4*l);
   if l = 1 then cols := []; else cols := Collected(FactorsInt(l)); fi;
   tot := 0;
   for L in cf_c_A(nu0) do                                  # L in A(nu_0), cyclic
      if not cf_feasible(cols, L) then continue; fi;
      Us   := List(cols, x-> cf_Udata(x[1], x[2], L));
      tabs := List(L.primes, cf_tab);
      typs := List(L.sylow, x-> Position([[1,1],[2,1],[2,2]], x));
      nq   := Length(typs);
      m    := Length(cols);
      prof := EmptyPlist(m);
      it   := IteratorOfCartesianProduct(Us);
      while not IsDoneIterator(it) do
         tup  := NextIterator(it);
         mult := 1;
         for i in [1..m] do prof[i] := tup[i][1]; mult := mult * tup[i][2]; od;
         R    := Filtered([1..m], i-> prof[i].theta = 2);
         r    := Length(R);
         bs   := List([1..nq], k-> cf_KqtBase(typs[k], tabs[k], prof, k));
         tt   := List(prof, cf_Ttab);                       # tables for cf_h
         lms  := ListWithIdenticalEntries(m, 0);            # column characters
         vx   := ListWithIdenticalEntries(m, 0);            # reused for every xi
         P1   := ListWithIdenticalEntries(m, 0);            # reused for every psi
         nal  := 2;                                         # |Aut(C_4)|
         for mx in [0..2^r-1] do                            # xi in Theta(U)
            for k in [1..r] do vx[R[k]] := QuoInt(mx, 2^(k-1)) mod 2; od;
            for al in [0,1] do                              # alpha in Aut(C_4)
               for mp in [0..2^r-1] do                      # psi
                  for k in [1..r] do
                     P1[R[k]] := QuoInt(mp, 2^(k-1)) mod 2;
                  od;
                  h := cf_h("C4", tt, vx, al, 0, [P1]);
                  if not h = 0 then
                     for i in [1..m] do lms[i] := vx[i] + 2*P1[i]; od;
                     w := cf_KUL(prof, typs, tabs, lms, bs);
                     tot := tot + mult * h * w / (2^r * nal);
                  fi;
               od;
            od;
         od;
      od;
   od;
   return tot;
end;

#####################################################
## input: a cubefree integer n >= 1 whose graph Gamma(n) is connected
## output: gnu_cyc(n), evaluated by the restricted sums of Theorem 4.11: the
##         summand s = 1, and only the socle orders l that are squarefree and
##         coprime to the order nu = n/(d*l) of the socle complement
##
cf_c_gnu_connected := function(n)
local tot, d, l, t;
   tot := 0;
   for d in DivisorsInt(cf_Q(n)) do                  # d = order of the Frattini subgroup
      for l in DivisorsInt(n/d) do                   # l = order of the socle
         if not cf_Q(l) = 1 then continue; fi;       # (b) l squarefree
         if not Gcd(l, n/(d*l)) = 1 then continue; fi;   # (c) gcd(l,nu) = 1
         t := cf_vq(n/(d*l), 2);
         if   t = 0 then tot := tot + cf_c_gnu_phi_0(n/d, l);
         elif t = 1 then tot := tot + cf_c_gnu_phi_1(n/d, l);
         else            tot := tot + cf_c_gnu_phi_2(n/d, l);
         fi;
      od;
   od;
   return tot;
end;

#####################################################
## input: a cubefree integer n >= 1
## output: gnu_cyc(n), the number of groups of order n all of whose Sylow
##         subgroups are cyclic
##
NumberCubefreeCGroups := function(n)
   if not IsPosInt(n) then
      Error("NumberCubefreeCGroups: <n> must be a positive integer");
   fi;
   if ForAny(Collected(FactorsInt(n)), x-> x[2] > 2) then
      Error("NumberCubefreeCGroups: <n> must be cubefree");
   fi;
   if n = 1 then return 1; fi;
   return Product(cf_components(n), cf_c_gnu_connected);
end;

