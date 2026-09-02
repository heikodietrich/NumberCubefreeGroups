###
### Test file accompanying cubefree-enum.gap
###
### For cross-checking: once loaded, cubefree_db_orders is a list of pairs [ n, gnu(n) ]
### where most values of gnu(n) have been computed with NumberCFGroups of Cubefree Version 1.22
### In particular, it contains all cross-checked cubefree n<10^6 and the large orders in Table 2
###
### Start the test with 
###        cubefree_test_against_DB( bound )
### This will run over the first 'bound' entries of cubefree_db_orders (loaded from cf_db.g)
###

Read("cubefree-enum.gap");
Read("cf_db.g");

cubefree_db_orders:=cubefree_db;


######################################################
##
## Test of our gnu(n) against cubefree_db_orders
##

#####################################################
##
cubefree_test_against_DB := function(arg)
local gnu, bad, cnt, tot, tmax, nmax, p, n, t, mynum, ok,bound,DB;

   if Length(arg)=1 then bound:=arg[1]; DB := cubefree_db_orders; fi;
   if Length(arg)=2 then bound:=arg[1]; DB := arg[2]; fi;
   bad := [];  cnt := 0;  tot := 0;  tmax := -1;  nmax := 0;

   Display("do not test prime orders");

   for p in DB do
      n := p[1];
      if cnt <= bound and not IsPrimeInt(n) then
         cnt := cnt + 1;

         t := Runtime();
         mynum := NumberCubefreeGroups(n);
         t := Runtime() - t;

         tot := tot + t;
         if t > tmax then tmax := t;  nmax := n;  fi;

         if mynum = p[2] then
            ok := "OK";
         else
            ok := "MISMATCH";
            Add(bad, [n, mynum, p[2]]);
         fi;

         Print(n, "   NumberCubefreeGroups = ", mynum, "   GAP gnu = ", p[2], "   ",
               ok, "   [", t, " ms]\n");
      fi;
   od;

   Print("\n");
   Print("tested        : ", cnt, " cube-free orders <= ", bound, "\n");
   Print("mismatches    : ", Length(bad), "\n");
   if cnt > 0 then
      Print("total time    : ", tot, " ms\n");
      Print("average time  : ", Float(tot)/Float(cnt), " ms\n");
      Print("maximal time  : ", tmax, " ms   (n = ", nmax, ")\n");
   fi;
   if not bad = [] then
      Print("[n, gnu_cf(n), gnu(n)]: ",
            bad{[1..Minimum(10, Length(bad))]}, "\n");
   fi;

   return bad;
end;

