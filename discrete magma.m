// The following file contains code to run the function "IsDiscrete", which
// determines if a two-generator subgroup of SL(2,Qp) is discrete

// input A, B, p, (optional: precision)	  where p is prime and A, B in SL(2, Q_p) representing
//					  elts of PSL(2,Q_p), and precision=20 unless o/wise specified
// output:
//   true, "isomorphism type of G"        if G=<A,B> is discrete in PSL(2, Q_p)
//   false, _                             if G not discrete
//   "error", "precision too low".        ord(B);if precision argument needs to be increased

// we first define translation length of element of PSL(2, Q_p)
TL := function (X, p)
   return -2*Min (0, Valuation (pAdicField(p)!Trace (X)));
end function;

// function to find order of an element of PSL(2, Q_p), returns 0 if infinite order
ord := function (m, p)
   I := Matrix(2, [1 , 0, 0, 1]);
   S := Sort( [ s : s in {2,3} join Set(Divisors(p+1)) join Set(Divisors(p-1)) ]);
   for i in S do
      if m^i in {I, -I} then
         if IsOdd(i) or m^i in {-I} then return i;
         else return i/2;
         end if;
      end if;
   end for;
   return 0;
end function;

// function to identify finite two-generator subgroups of PSL(2, Q_p)
id := function (u, v, p)

   ord := function (m)
      return ord(m,p);
   end function;

   if 0 in {ord(u), ord(v)} then return "infinite";
   elif ord(u*v*u^-1*v^-1) eq 1 then return GroupName(CyclicGroup(Lcm(ord(u),ord(v))));
   else
      if ord(u) gt ord(v) then
         x := v; y := u;
      else
         x := u; y := v;
      end if;

      S := [ ord(x), ord(y) ];
      if 0 in {ord(x*y)} then return "infinite";
      elif ord(x) eq 2 and ord(x*y) eq 2 then return GroupName(DihedralGroup(ord(y)));
      elif S eq [2,2] then return GroupName(DihedralGroup(ord(x*y)));
      elif S eq [2,3] then
         if ord(x*y) eq 3 then return GroupName(AlternatingGroup(4));
         elif ord(x*y) eq 4 then return GroupName(SymmetricGroup(4));
         elif ord(x*y) eq 5 then return GroupName(AlternatingGroup(5));
         end if;
      elif S eq [2,4] and ord(x*y) eq 3 then return GroupName(SymmetricGroup(4));
      elif S eq [2,5] and 3 in {ord(x*y), ord(x*y^2)} then return GroupName(AlternatingGroup(5));
      elif S eq [3,3] then
         if 2 in {ord(x*y), ord(x^-1*y)} then return GroupName(AlternatingGroup(4));
         elif {2} eq {ord(x*y*x^-1*y), ord(x*y*x*y^-1)} then return GroupName(AlternatingGroup(5));
         end if;
      elif S eq [3,4] and 2 in {ord(x*y), ord(x^-1*y)} then return GroupName(SymmetricGroup(4));
      elif S eq [3,5] and ( 2 in {ord(x*y), ord(x^-1*y)} or [3,2] eq [ord(x*y), ord(x*y^3)]
      or [3,2] eq [ord(x^-1*y), ord(x*y^2)] ) then
         return GroupName(AlternatingGroup(5));
      elif S eq [4,4] and {2} eq {ord(x*y^2), ord(x^2*y)} and 1 eq ord(x*y*x*y^-1*x^-1*y^-1) then
         return GroupName(SymmetricGroup(4));
      elif S eq [5,5] and ( {2,3} eq {ord(x*y), ord(x^-1*y)}
      or ( [2,1] eq [ord(x*y^-1*x), ord(x*y*x^-1*y*x*y^-1)] )
      or ( [2,1] eq [ord(x*y*x), ord(x*y*x*y^-1*x^-1*y^-1)] ) ) then
         return GroupName(AlternatingGroup(5));
      end if;
   end if;
   return "infinite";
end function;


// function to compute minimal non-positive p-adic valuation across
// 2 matrices
min_val := function (u, v, p)
   S := { Valuation(pAdicField(p)!u[i,j]) : i,j in {1,2} };
   T := { Valuation(pAdicField(p)!v[i,j]) : i,j in {1,2} };
   return Min( {0} join S join T );
end function;


// we now define the function "IsDiscrete"

IsDiscrete := function (A, B, p : precision:=20)
   K := pAdicField(p, precision);

   assert Type (A) eq AlgMatElt and Type (B) eq AlgMatElt;
   assert Determinant(A) in {1};
   assert Determinant(B) in {1};
   for i,j in [1..2] do
      assert A[i][j] in K and B[i][j] in K;
   end for;

   // check finiteness of G
   if id(A,B,p) ne "infinite" then return true, ", G is finite and isomorphic to", id(A,B,p);
   end if;

   // initialise generators
   X := A;
   Y := B;

   // performing translation length minimising procedure
   if Min ( TL(X, p) , TL(Y, p) ) ne 0 then
     num_steps := 0;
      repeat
         a := TL (X*Y, p); b := TL (X^-1 * Y, p); m := Min (a, b);
         l1 := TL (X, p); l2 := TL (Y, p);
         if l1 ge l2 and m eq a then
            X := X*Y; num_steps+:=1;
         elif l1 ge l2 and m eq b then
            X := X^-1*Y; num_steps+:=1;
         elif l1 lt l2 and m eq a then
            Y := X*Y; num_steps+:=1;
         elif l1 lt l2 and m eq b then
            Y := X^-1*Y; num_steps+:=1;
         end if;

         free := m gt Abs ( l1 - l2 );
         elliptic := Min ( l1 , l2 ) eq 0;
         precision_error := num_steps*-min_val(X, Y, p) gt precision or Determinant(X) notin {1}
                            or Determinant(Y) notin {1};
      until free or elliptic or precision_error;
      if precision_error then return "error", "precision too low";
      elif free then return true, ", G is discrete and free of rank two";
      end if;
   end if;


   // set X to be elliptic
   if TL (X, p) ne 0 then
      S := [ X, Y ];
      X := S[2];
      Y := S[1];
   end if;

   // G is not discrete if X infinite order, otherwise replace Y by X^i*Y if smaller TL
   n := ord(X, p);
   if n eq 0 then return false, _;
   else
      for i in [1..n-1] do
         if TL (X^i*Y, p) lt TL (Y, p) then Y := X^i*Y;
         end if;
      end for;
   end if;

   // checking for free product of two elliptic subgroups
   if TL (Y, p) eq 0 then
      m := ord(Y, p);
      if m eq 0 or TL ( X*Y, p ) eq 0 then return false, _;
      else return true, ", G is isomorphic to free product of", GroupName(CyclicGroup(n)),
         "and", GroupName(CyclicGroup(m));
      end if;
    end if;

   // checking for free product of elliptic and hyperbolic
   comm := X*Y*X^-1*Y^-1;
   if TL ( comm, p ) gt 0 then
      return true, ", G is isomorphic to free product of", GroupName(CyclicGroup(n)),
         "and Z";
   // checking for infinite order elliptics
   elif ord(comm, p) eq 0 then
      return false, _;
   // checking for commuting generators
   elif ord(comm, p) eq 1 then
      return true, ", G is isomorphic to direct product of", GroupName(CyclicGroup(n)),
         "and Z";
   // checking for infinite order elliptics
   elif TL ( X * Y^2 * X^-1 * Y^-2, p ) eq 0 then
      return false, _;
   end if;

   // final cases depending on G_0=<X,YXY^-1>
   G0 := id(X, Y*X*Y^-1, p);
   if G0 eq "infinite" then
      return false, _;
   elif G0 in {"S4", "A5"} then
      return true, ", G is an amalgamated free product of", G0, "and", GroupName(DihedralGroup(n)),
      "over", GroupName(CyclicGroup(n));
   elif G0 eq "A4" then
      for i,j,k in [0..2] do
         g := X^i*Y*X^j*Y^-1*X^k;
         if { ord(g, p), ord(g*Y, p) } eq {2} then
            return true, ",G is an amalgamated free product of", G0, "and", GroupName(DihedralGroup(n)),
            "over", GroupName(CyclicGroup(n));
         end if;
      end for;
      return true, ", G is an HNN extension of", G0;
   else
      prod := X*Y*X*Y^-1;
      m := ord( prod, p);
      for i in [0..m-1] do
         g := (prod)^i*X;
         if { ord(g, p), ord(g*Y, p) } eq {2} then
            return true, ",G is an amalgamated free product of", G0, "and", GroupName(SmallGroup(4,2)),
            "over", GroupName(CyclicGroup(n));
         end if;
      end for;
      return true, ", G is an HNN extension of", G0;
   end if;

end function;



// EXAMPLE OF Z * Z in Q_5

p:=5;
K := pAdicField(p);
A := Matrix(2, [p , p-1, -1/p, 1/p^2]);
B := Matrix(2, [2/p^4 , p^3, 1/p^3, p^4]);
IsDiscrete(A,B,p);

// EXAMPLE OF C2 * C3 in Q_7

p := 7;
K := pAdicField(p);
t := 0;
s := 1;
A := Matrix(2, [0 , -1, 1, t]);
B := Matrix(2, [0 , -1/p, p, s]);
IsDiscrete(A,B,p);


// EXAMPLE OF C2 * C5 in Q_11

p := 11;
K := pAdicField(p);
O := RingOfIntegers(K);
R<x> := PolynomialRing(K);
t :=0;
s := Roots(x^2-x-1)[1][1];
A := Matrix(2, [0 , -1, 1, t]);
B := Matrix(2, [0 , -1/p, p, s]);
IsDiscrete(A,B,p);

// EXAMPLE OF C2 * Z in Q_7

p := 7;
K := pAdicField(p);
t := 0;
A := Matrix(2, [0 , p^2, -1/p^2, t]);
B := Matrix(2, [p^2 , p-1, 1, 1/p]);
IsDiscrete(A,B,p);

// EXAMPLE OF C4 * Z in Q_7

p := 7;
K := pAdicField(p);
O := RingOfIntegers(K);
R<x> := PolynomialRing(K);
t := Roots(x^2-2)[1][1];
A := Matrix(2, [0 , p^2, -1/p^2, t]);
B := Matrix(2, [p^2 , p-1, 1, 1/p]);
IsDiscrete(A,B,p);


// EXAMPLE OF C3xZ in Q_7

p := 7;
K := pAdicField(p);
O := RingOfIntegers(K);
R<x> := PolynomialRing(K);
a := Roots(x^3-1)[2][1];
A := Matrix(2, [a , 0, 0, a^-1]);
B := Matrix(2, [p, 0, 0, 1/p]);
IsDiscrete(A,B,p);


// EXAMPLE OF HNN EXT OF D3 in Q_13

p := 13;
K := pAdicField(p);
O := RingOfIntegers(K);
R<x> := PolynomialRing(K);
t := 0;
w := Roots(x^6-1)[3][1];
s := w + w^-1;
a := Roots((x^2-t*x+1)*(2-p^2-1/p^2)+t^2-2-s)[1][1];
A := Matrix(2, [a , 1, a*(t-a)-1, t-a]);
B := Matrix(2, [p, 0, 0, 1/p]);
IsDiscrete(A,B,p);


// EXAMPLE OF HNN EXT OF A4 in Q_7

p := 7;
K := pAdicField(p);
O := RingOfIntegers(K);
R<x> := PolynomialRing(K);
t := 1;
s := 1;
a := Roots((x^2-t*x+1)*(2-p^2-1/p^2)+t^2-2-s)[1][1];
A := Matrix(2, [a , 1, a*(t-a)-1, t-a]);
B := Matrix(2, [p, 0, 0, 1/p]);
IsDiscrete(A,B,p);


// EXAMPLE OF D3 *_C2 D2 in Q_13

p := 13;
K := pAdicField(p);
O := RingOfIntegers(K);
R<x> := PolynomialRing(K);
t := 0;
w := Roots(x^6-1)[2][1];
s := w + w^-1;
a := Roots((x^2-t*x+1)*(2-p^2-1/p^2)+t^2-2-s)[1][1];
A := Matrix(2, [a , 1, a*(t-a)-1, t-a]);
B := Matrix(2, [p, 0, 0, 1/p]);
IsDiscrete(A,B,p);

// EXAMPLE OF A4 *_C3 D3 in Q_7

p := 7;
K := pAdicField(p);
O := RingOfIntegers(K);
R<x> := PolynomialRing(K);
t := 1;
s := 0;
a := Roots((x^2-t*x+1)*(2-p^2-1/p^2)+t^2-2-s)[1][1];
A := Matrix(2, [a , 1, a*(t-a)-1, t-a]);
B := Matrix(2, [p, 0, 0, 1/p]);
IsDiscrete(A,B,p);

// EXAMPLE OF S4 *_C4 D4 in Q_17

p := 17;
K := pAdicField(p);
O := RingOfIntegers(K);
R<x> := PolynomialRing(K);
t := Roots(x^2-2)[1][1];
s := 1;
a := Roots((x^2-t*x+1)*(2-p^2-1/p^2)+t^2-2-s)[1][1];
A := Matrix(2, [a , 1, a*(t-a)-1, t-a]);
B := Matrix(2, [p, 0, 0, 1/p]);
IsDiscrete(A,B,p);

// EXAMPLE OF A5 *_C3 D3 in Q_19

p := 19;
K := pAdicField(p);
O := RingOfIntegers(K);
R<x> := PolynomialRing(K);
t := 1;
s := Roots(x^2-x-1)[1][1];
a := Roots((x^2-t*x+1)*(2-p^2-1/p^2)+t^2-2-s)[1][1];
A := Matrix(2, [a , 1, a*(t-a)-1, t-a]);
B := Matrix(2, [p, 0, 0, 1/p]);
IsDiscrete(A,B,p);


// EXAMPLE OF A5 *_C5 D5 in Q_11

p := 11;
K := pAdicField(p);
O := RingOfIntegers(K);
R<x> := PolynomialRing(K);
t := Roots(x^2-x-1)[1][1];
s := 1;
a := Roots((x^2-t*x+1)*(2-p^2-1/p^2)+t^2-2-s)[1][1];
A := Matrix(2, [a , 1, a*(t-a)-1, t-a]);
B := Matrix(2, [p, 0, 0, 1/p]);
IsDiscrete(A,B,p);

