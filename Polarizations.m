/*
VERSION 2025-02-10

--------------------------------------------------------------------------------

This collection of Magma routines is associated with the paper

     Principally polarized squares of elliptic curves
           with field of moduli equal to Q
        
by Alexander Gélin, Everett W. Howe, and Christophe Ritzenthaler
[GélinHoweRitzenthaler2019].

--------------------------------------------------------------------------------

Change log:

2025-02-10:
Used a different matrix M in the comment describing the action of the 2-torsion
on the polarizations, which leads to simpler formulas for newN1, newN2, and
newalpha. Using these formulas in polarizations() leads to a noticeable speedup.

Cleaned up comments. Updated references.

2024-09-05: 
The previous version assumed that the quadratic field we were dealing with have 
class group of exponent dividing 2. This was sufficient for the purposes of our
application to curves over Q with Jacobians isomorphic to E x E, where E has CM
by a maximal quadratic order. But in the paper we described algorithms that work
more generally. This revision provides implementations of the more general
algorithm, including some improvements that did not get mentioned in the paper.
The code has been significantly rewritten, with more extensive documentation.

To keep notation here similar to that of the paper, we have swapped the role
of alpha and alpha-bar in the definition of the polarization associated to a
triple [N1, N2, alpha]. In the previous version of the code, alpha was the 
bottom left entry of the polarization matrix; now it is the top right.

2018-06-11: First public version.

--------------------------------------------------------------------------------

Bibliography:

[GélinHoweRitzenthaler2019]
Alexander Gélin, Everett W. Howe, and Christophe Ritzenthaler:
Principally polarized squares of elliptic curves with field of moduli equal to Q,
pp. 257–274 in:
ANTS XIII: Proceedings of the Thirteenth Algorithmic Number Theory Symposium 
(R. Scheidler and J. Sorenson, eds.), 
the Open Book Series 2, Mathematical Sciences Publishers, Berkeley, 2019.
https://doi.org/10.2140/obs.2019.2.257

[Hatashida1968]
Tsuyoshi Hayashida:
A class number associated with the product of an elliptic curve with itself,
J. Math. Soc. Japan 20 (1968), 26–43.
https://doi.org/10.2969/jmsj/02010026

--------------------------------------------------------------------------------

The programs in this file will compute reduced forms for all of the positive 
definite unimodular binary Hermitian forms over an imaginary quadratic maximal
order O that does not contain any roots of unity other than 1 and -1.

Each reduced form is labeled as being either split (decomposable) or nonsplit
(indecomposable), and the automorphism group of the form is provided (as a list
of matrices).

-----

Notation:

Delta will be an imaginary fundamental discriminant.
O will be the corresponding maximal order.

Polarizations P will be given by sequences [N1, N2, alpha] with alpha in O and
with 0 < N1 <= N2 and N1*N2 - Norm(alpha) = 1.
Such a P will correspond to the matrix [N1, alpha; alpha-bar, N2].

The function

     HayashidaCountCurves(Delta)

computes Hayashida's count of the number of curves of genus 2 with Jacobian 
isomorphic to E x E, where E is an elliptic curve with CM by Delta. This formula
is found on pages 42–43 of [Hatashida1968], but there is a typographical error
on page 43. The expression

(1-(-1))^{(m^2-1)/8}

should be

(1-(-1)^{(m^2-1)/8}) h.

The function

     HayashidaCountPolarizations(Delta) 

computes the total number of principal polarizations on E x E (up to 
isomorphism), where E is an elliptic curve with CM by Delta. 

The function 

     polarizations(Delta)
    
will attempt to compute reduced representatives for all of the positive 
definite unimodular binary Hermitian forms over the (maximal) order of 
discriminant Delta < -4. The program may fail: It precomputes all elements of O
of norm up to f*Delta^2 for a parameter f that defaults to Log(-Delta). If it
turns out that the computation needs elements of larger norm, the program will
fail in a not-particularly-graceful way. You can tell the program to use a 
larger value of f by specifying f when you call the function:

     polarizations(Delta : f := <the value you choose>)
    
If it succeeds, the program outputs a list of triples 
     <P, splitting-type, automorphism-group>
where P is a polarization as described above, splitting-type is either "split"
or "nonsplit", and automorphism-group is a list of all of the elements of
GL(2,O) that preserve the polarization.


--------------------------------------------------------------------------------

To verify the statements in [GélinHoweRitzenthaler2019] about the number of
nonsplit polarizations for the discriminants we are considering, simply run the
command VerifyPaperStatements(). It returns a boolean value that is true if and
only if the counts of nonsplit polarizations match those in Table 2 of the
paper, together with a (long) list of all of the polarizations for all of the
discriminants.

*/

//------------------------------------------------------------------------------

function HayashidaCountCurves(Delta)
// Delta is a negative fundamental discriminant. We output the number of curves
// having Jacobian isomorphic to E x E, where E is a fixed elliptic curve with 
// CM by the imaginary quadratic order of discriminant Delta. We use the formula
// from [Hayashida1968] mentioned above, with the correction mentioned above.

  if not IsFundamentalDiscriminant(Delta) or not Delta lt 0 then
    error "Input must be a negative fundamental discriminant.";
  end if;
  
  if 0 eq Delta mod 4 then
    m := Integers()!(-Delta/4);
  else 
    m := Integers()!-Delta;
  end if;

 // Deal with the small cases: Delta = -3, Delta = -4, and Delta = -8.
  case m:
    when 1: return 0;
    when 2: return 1;
    when 3: return 0;
  end case;

  pb := PrimeBasis(m);
  t := #PrimeBasis(-Delta);
  h := ClassNumber(Delta);

  // Hayashida's formula depends on the value of m mod 8, so we break into
  // cases.
  
  if 3 eq m mod 4 then
    H := (1/24)* &*[p + (-1)^((p-1) div 2) : p in pb]
         + (1/6) * &*[1 + (-1)^((p-1) div 2) * LegendreSymbol(p,3) : p in pb ]
         + (1/4) * (1 - (-1)^((m^2-1) div 8)) * h  // HAYASHIDA'S TYPO CORRECTED
         - 2^(t-3);
  end if;
  
  if 1 eq m mod 4 then
    H := (1/8)* &*[p + (-1)^((p-1) div 2) : p in pb]
         + (1/4) * h 
         - 2^(t-4);
  end if;
  
  if 2 eq m mod 8 then
    H := (7/24)* &*[p + (-1)^((p-1) div 2) : p in pb | p ne 2]
         + (1/3) * &*[1 + (-1)^((p-1) div 2) * LegendreSymbol(p,3) : p in pb | p ne 2]
         + (1/4) * h 
         - 2^(t-4);
  end if;
  
  if 6 eq m mod 8 then
    H := (3/8)* &*[p + (-1)^((p-1) div 2) : p in pb | p ne 2]
         + (1/4) * h 
         - 2^(t-4);
  end if;
  
  return Integers()!H;
end function;


//------------------------------------------------------------------------------

function HayashidaCountPolarizations(Delta)
// Again, Delta is assumed to be a negative fundemental discriminant. 
// We return the number of nonisomorphic principal polarizations on E x E, where
// E is an arbitrary elliptic curve with CM by the imaginary quadratic order of
// discriminant Delta. This is the sum H + h_2, where H is the count of curves
// with Jacobian E x E (computed by the preceding function) and where h_2 is the
// number of isomorphism class of split polarizations, which Hayashida shows is
// equal to (h + 2^{t-1})/2, where t is the number of distinct prime factors of
// Delta; see Section 2 of [Hatashida1968]. Note thaht 2^{t-1} is equal to the
// size of the 2-torsion subgroup of the class group of Delta, by genus theory.
// This formula is also Corollary 3.4 of [GélinHoweRitzenthaler2019].

  if not IsFundamentalDiscriminant(Delta) or not Delta lt 0 then
    error "Input must be a negative fundamental discriminant.";
  end if;
  
  curves := HayashidaCountCurves(Delta);
  twotorsion := 2^(#PrimeBasis(-Delta)-1);
  h := ClassNumber(Delta);
  split := (h + twotorsion) div 2;
  return curves + split;
end function;


//------------------------------------------------------------------------------

function conjugate(x)
// Utility function to compute the Galois conjugate of an element of a quadratic
// field.
  return Trace(x) - x;
end function;


//------------------------------------------------------------------------------

function conjugate_transpose(M)
// Utility function to return the conjugate transpose of a 2 x 2 matrix with
// entries in a quadratic field.
  return Transpose(Matrix(2,[conjugate(a) : a in Eltseq(M)]));
end function;


//------------------------------------------------------------------------------

procedure compute_automorphisms(~P,~elements,~starting,~ending,~autos)
// Procedure to compute the automorphisms of a polarization on E x E. Here
// P is the polarization, represented by a triple [N1, N2, alpha] as described
// at the top of this file. The variable autos will be filled with the 
// automorphisms of the polarized variety (E x E, P), with each automorphism
// represented by a 2 x 2 matrix with entries in O that we take to act on E x E.
// The variable elements contains a list of elements of O of small norm, sorted
// by norm. The variables starting and ending have the property that
// starting[n+1] and ending[n+1] indicate where in the variable elements one
// finds the first element of norm n and the last element of norm n. If there
// are no such elements, then starting[n+1] = ending[n+1] = -1.

  N1 := Integers()!P[1];
  N2 := Integers()!P[2];
  alpha := P[3];
  alphabar := conjugate(alpha);
  
  O := Parent(alpha);
  
  // The matrix giving the polarization:
  Pmatrix := Matrix(2,[N1,alpha,alphabar,N2]);

  // Initialize the list of automorphisms.
  autos := [];
  
  // An automorphism of (E x E, P) must take the vector [1,0] to a vector
  // whose length is equal to N1, where the length of a vector V is the value
  // (conjugate transpose of V) * P * V. It must also take [0,1] to a vector
  // of length N2. We find all possible pairs of such vectors and compute which
  // pairs give rise to an automorphism. 
  
  // The sequence normN1 will end up containing vectors in O x O whose lengths
  // are equal to N1.
  
  normN1 := []; 
  
  // To compute the vectors of length N1, we use Remark 3.7 from
  // [GélinHoweRitzenthaler2019]. If [x,y] has length n, then we have
  // Norm(N1*x + alpha*y) + Norm(y) = n*N1. So to find vectors of length N1,
  // we let y range over elements of norm up to N1*N1, and then we let z range 
  // over elements of norm N1*N1 - Norm(y), and for each z we check whether
  // z - alpha*y is divisible by N1 in O, in which case we set 
  // x = (z - alpha*y)/N1.

  for ynorm in [0..N1*N1] do
    linearnorm := N1*N1 - ynorm;
    if starting[ynorm+1] ne -1 and starting[linearnorm+1] ne -1 then
      ys := [elements[i] : i in [starting[ynorm+1]..ending[ynorm+1]]];
      linears := [elements[i] : i in [starting[linearnorm+1]..ending[linearnorm+1]]];
      for lin in linears, y in ys do
        x := (lin - alpha*y)/N1;
        if x in O then
          normN1 cat:= [[O!x,y]];
        end if;
      end for;
    end if;
  end for;

  // Now we use the same method to calculate the vectors of length N2.
  normN2 := [];

  for ynorm in [0..N1*N2] do
    linearnorm := N1*N2 - ynorm;
    if starting[ynorm+1] ne -1 and starting[linearnorm+1] ne -1 then
      ys := [elements[i] : i in [starting[ynorm+1]..ending[ynorm+1]]];
      linears := [elements[i] : i in [starting[linearnorm+1]..ending[linearnorm+1]]];
      for lin in linears, y in ys do
        x := (lin - alpha*y)/N1;
        if x in O then
          normN2 cat:= [[O!x,y]];
        end if;
      end for;
    end if;
  end for;
  
  // Now for each pair u, v of vectors, we see whether the map that sends [1,0]
  // to u and [0,1] to v gives an automorphism.

  for u in normN1, v in normN2 do
    mat := Matrix(2,[u[1],v[1],u[2],v[2]]);
    matbar := Matrix(2,[conjugate(u[1]),conjugate(u[2]),conjugate(v[1]),conjugate(v[2])]);
    if matbar * Pmatrix * mat eq Pmatrix then
      autos cat:= [mat];
    end if;
  end for;

end procedure;


//------------------------------------------------------------------------------

procedure reduce_polarization(~P,~elements,~starting,~ending : verbose := false)
// Given a polarization P and variables elements, starting, and ending (as 
// described in the comments to the preceding procedure), we find the smallest
// equivalent polarization. Here "smallest" means that if the polarization is
// [N1, N2, alpha], then N1 is as small as possible, and N2 is as small as
// possible given the value of N1, and alpha satisfies the following condition
// (given N1 and N2):  Consider the set of alphas obtained in equivalent 
// polarizations (with the given N1 and N2) with the smallest non-negative
// trace. If there is only one such alpha, choose it. Otherwise, choose the one
// with positive imaginary part.

  alerted := false;
  P1 := Integers()!P[1];
  P2 := Integers()!P[2];
  alpha := P[3];
  
  if P1 gt P2 then
    P1 := Integers()!P[2];
    P2 := Integers()!P[1];
    alpha := conjugate(alpha);
    P := [P1,P2,alpha];
  end if;

  alphabar := conjugate(alpha);

  O := Parent(P[3]);
  Delta := Discriminant(O);

  if verbose then printf "Searching for vectors of length: "; end if;

  N1 := 0;
  repeat
    N1 +:= 1;
    if verbose then printf "%o ", N1; end if;
    if Norm(elements[#elements]) lt N1*P1 then
      error "We did not precompute enough norms.";
    end if;

    // This variable will contain vectors of norm N1.
    shorts1 := []; 

    for ynorm in [0..N1*P1] do
      linearnorm := N1*P1 - ynorm;
      if starting[ynorm+1] ne -1 and starting[linearnorm+1] ne -1 then
        ys := [elements[i] : i in [starting[ynorm+1]..ending[ynorm+1]]];
        linears := [elements[i] : i in [starting[linearnorm+1]..ending[linearnorm+1]]];
        for lin in linears, y in ys do
          x := (lin - alpha*y)/P1;
          if x in O then
            shorts1 cat:= [[O!x,y]];
          end if;
        end for;
      end if;
    end for;

    primitiveshorts1 := [v : v in shorts1 | 1 eq Norm(ideal<O | v[1],v[2]>)];
  until #primitiveshorts1 gt 0;

  if verbose then printf "\n\nFound a primitive vector of length %o!\n\n", N1; end if;

  // We've found short vectors that are part of a basis. Let's rewrite our
  // polarization on the new basis. That will (possibly) reduce the size of P1,
  // and it will make it clear that the second coordinate of the other basis
  // vector will have to be a unit. Do this for all short vectors 
  // simultaneously.
  
  Pmatrix := Matrix(2,[P1,alpha,alphabar,P2]);

  newpols := [];

  for uv in primitiveshorts1 do
    u := uv[1];
    v := uv[2];
    if u*v eq 0 then
      if u eq 0 then uprime := 0; vprime := v; end if;
      if v eq 0 then uprime := u; vprime := 0; end if;
    else
      bool, uprime,vprime := Idempotents(ideal<O|u>,ideal<O|v>);
      assert bool;
      uprime := O!(uprime/u);
      vprime := O!(vprime/v);
    end if;
    assert 1 eq u*uprime + v*vprime;
    Mmatrix := Matrix(2,[u,-vprime,v,uprime]);
    Mmatrixstar := Matrix(2,[conjugate(u),conjugate(v),-conjugate(vprime),conjugate(uprime)]);
    newPmatrix := Mmatrixstar * Pmatrix * Mmatrix;
    newP1 := newPmatrix[1,1];
    newP2 := newPmatrix[2,2];
    newPalpha := newPmatrix[1,2];
    assert newP1 eq N1;
    newP1 := Integers()!newP1;
    newP2 := Integers()!newP2;
    newPalpha := O!newPalpha;
    newP := [newP1,newP2,newPalpha];
    newpols cat:= [newP];
  end for;

  if verbose then printf "Searching for vectors of length: "; end if;

  N2 := N1-1;
  repeat 
    N2 +:= 1;
    if verbose then printf "%o ", N2; end if;

    if Norm(elements[#elements]) lt N2*N1 then
      error "We did not precompute enough norms.";
    end if;

    allshorts2 := [];
    ys := [O!1,-1];
    
    for Q in newpols do
      // The following variable will contain vectors of norm N2.
      shorts2 := []; 
      linearnorm := N2*N1-1;
      if starting[linearnorm+1] eq -1 then
        linears := [];
      else
        linears := [elements[i] : i in [starting[linearnorm+1]..ending[linearnorm+1]]];
        for lin in linears, y in ys do
          x := (lin - Q[3]*y)/N1;
          if x in O then
            shorts2 cat:= [[O!x,y]];
          end if;
        end for;
      end if;
      allshorts2 cat:= [shorts2];
    end for;

  until &+[#z : z in allshorts2] gt 0;
  
  newalphas := [];
  for i in [1..#newpols] do
    Q := newpols[i];
    for v2 in allshorts2[i] do
      // The new value of alpha is our original vector [1,0] of length N1
      // paired with our new vector v2 of length N2. Since 1 and 0 are 
      // stable under conjugation, this value is
      // [1, 0] * [ Q[1]     Q[3] ] * [ v2[1] ] = Q[1]*v2[1] + Q[3]*v2[2].
      //          [ Q[3]-bar Q[2] ]   [ v2[2] ]
    
      newalphas cat:=[ Q[1]*v2[1] + Q[3]*v2[2] ];
    end for;
  end for;
  
  setalphas := Set(newalphas);
  mintrace := Min([Trace(a) : a in setalphas | Trace(a) ge 0]);
  newalphas := [a : a in setalphas | Trace(a) eq mintrace];
  
  if #newalphas eq 1 then
    new := newalphas[1];
  else
    new := [a : a in newalphas | Eltseq(a)[2] ge 0][1];
  end if;

  P := [N1,N2,O!new];
  
  if verbose then printf "\n\nReduced the polarization to %o.\n\n", P; end if;
end procedure;


//------------------------------------------------------------------------------

procedure set_reduced_flag(~P,~flag,~elements,~starting,~ending)
// Given a polarization on O x O, check to see whether it is reduced (as 
// defined above). The boolean variable "flag" will give the answer. The 
// variables elements, starting, and ending are as in the preceding procedures.

  alerted := false;
  P1 := Integers()!P[1];
  P2 := Integers()!P[2];
  alpha := P[3];
  
  if P1 gt P2 then
    flag:=false;
    return;
  end if;

  alphabar := conjugate(alpha);

  O := Parent(P[3]);
  Delta := Discriminant(O);

  N1 := 0;
  repeat
    N1 +:= 1;
    if Norm(elements[#elements]) lt N1*P1 then
      error Error("We did not precompute enough norms.");
    end if;
    
    shorts1 := []; // will contain vectors of norm N1

    for ynorm in [0..N1*P1] do
      linearnorm := N1*P1 - ynorm;
      if starting[ynorm+1] ne -1 and starting[linearnorm+1] ne -1 then
        ys := [elements[i] : i in [starting[ynorm+1]..ending[ynorm+1]]];
        linears := [elements[i] : i in [starting[linearnorm+1]..ending[linearnorm+1]]];
        for lin in linears, y in ys do
          x := (lin - alpha*y)/P1;
          if x in O then
            shorts1 cat:= [[O!x,y]];
          end if;
        end for;
      end if;
    end for;

    primitiveshorts1 := [v : v in shorts1 | 1 eq Norm(ideal<O | v[1],v[2]>)];
  until #primitiveshorts1 gt 0;

  if N1 lt P1 then flag:=false; return; end if;

  // We've found short vectors that are part of a basis. Let's rewrite our
  // polarization on the new basis. That will (possibly) reduce the size of P1,
  // and it will make it clear that the second coordinate of the other basis
  // vector will have to be a unit. Do this for all short vectors 
  // simultaneously.
  
  Pmatrix := Matrix(2,[P1,alpha,alphabar,P2]);

  newpols := [];

  for uv in primitiveshorts1 do
    u := uv[1];
    v := uv[2];
    if u*v eq 0 then
      if u eq 0 then uprime := 0; vprime := v; end if;
      if v eq 0 then uprime := u; vprime := 0; end if;
    else
      bool, uprime,vprime := Idempotents(ideal<O|u>,ideal<O|v>);
      assert bool;
      uprime := O!(uprime/u);
      vprime := O!(vprime/v);
    end if;
    assert 1 eq u*uprime + v*vprime;
    Mmatrix := Matrix(2,[u,-vprime,v,uprime]);
    Mmatrixstar := Matrix(2,[conjugate(u),conjugate(v),-conjugate(vprime),conjugate(uprime)]);
    newPmatrix := Mmatrixstar * Pmatrix * Mmatrix;
    newP1 := newPmatrix[1,1];
    newP2 := newPmatrix[2,2];
    newPalpha := newPmatrix[2,1];
    assert newP1 eq N1;
    newP1 := Integers()!newP1;
    newP2 := Integers()!newP2;
    newPalpha := O!newPalpha;
    newP := [newP1,newP2,newPalpha];
    newpols cat:= [newP];
  end for;
    
  N2 := N1-1;
  repeat 
    N2 +:= 1;
    if Norm(elements[#elements]) lt N2*N1 then
      error Error("We did not precompute enough norms.");
    end if;
    
    allshorts2 := [];
    ys := [O!1,-1];
    
    for Q in newpols do
      shorts2 := []; 
      linearnorm := N1*N2-1;
      if starting[linearnorm+1] eq -1 then 
        linears := []; 
      else
        linears := [elements[i] : i in [starting[linearnorm+1]..ending[linearnorm+1]]];
        for lin in linears, y in ys do
          x := (lin - Q[3]*y)/N1;
          if x in O then
            shorts2 cat:= [[O!x,y]];
          end if;
        end for;
        allshorts2 cat:= [shorts2];
      end if;
    end for;
  until &+([0] cat [#z : z in allshorts2]) gt 0;

  if N2 ne P2 then flag:=false; return; end if;
  
  newalphas := [];
  for i in [1..#newpols] do
    Q := newpols[i];
    for v2 in allshorts2[i] do
      newalphas cat:=[ Q[1]*v2[1] + Q[3]*v2[2] ];
    end for;
  end for;
  
  setalphas := Set(newalphas);
  mintrace := Min([Trace(a) : a in setalphas | Trace(a) ge 0]);
  newalphas := [a : a in setalphas | Trace(a) eq mintrace];
  
  if #newalphas eq 1 then
    new := newalphas[1];
  else
    new := [a : a in newalphas | Eltseq(a)[2] ge 0][1];
  end if;

  flag := (P[3] eq O!new);
end procedure;


//------------------------------------------------------------------------------

function order2(Delta)
// Given a fundamental discriminant Delta, return generators (and extra 
// information) for class group elements of order 2.
// Namely, return n, alpha, x, y, where 
//      (n,alpha) is an ideal of order 2 in class group, and
//      n^2 * x - y * Norm(alpha) = n

  K := QuadraticField(Delta);
  O := MaximalOrder(K);
  ideals := [];

  case Delta mod 8:
    when 4:
      m := Delta div 4;
      assert O.2^2 eq m;
      for d in Divisors(-m) do
        if d^2 lt -m then
          n := d;
          alpha := O.2;
          g,x,y := ExtendedGreatestCommonDivisor(n^2,-Integers()!Norm(alpha));
          assert g eq n;
          assert x*n^2 - y*Norm(alpha) eq n;
          if d gt 1 then 
            ideals cat:= [<n,alpha,x,y>];
          end if;
          n := 2*d;
          const := (m mod (2*d));
          if const gt d then const-:=2*d; end if;
          alpha := O.2 + const;
          g,x,y := ExtendedGreatestCommonDivisor(n^2,-Integers()!Norm(alpha));
          assert g eq n;
          assert x*n^2 - y*Norm(alpha) eq n;
          ideals cat:= [<n,alpha,x,y>];
        end if;
      end for;
    when 0:
      m := Delta div 4;
      assert O.2^2 eq m;
      for d in Divisors(-m) do
        n := d;
        alpha := O.2;
        g,x,y := ExtendedGreatestCommonDivisor(n^2,-Integers()!Norm(alpha));
        assert g eq n;
        assert x*n^2 - y*Norm(alpha) eq n;
        if d gt 1 then 
          ideals cat:= [<n,alpha,x,y>];
        end if;
      end for;
    when 1:
      m := Delta;
      assert (2*O.2-1)^2 eq m;
      for d in Divisors(-m) do
        if d^2 lt -m then
          n := d;
          alpha := 2*O.2 - 1;
          g,x,y := ExtendedGreatestCommonDivisor(n^2,-Integers()!Norm(alpha));
          assert g eq n;
          assert x*n^2 - y*Norm(alpha) eq n;
          if d gt 1 then 
            ideals cat:= [<n,alpha,x,y>];
          end if;
        end if;
      end for;
    when 5:
      m := Delta;
      assert (2*O.2-1)^2 eq m;
      for d in Divisors(-m) do
        if d^2 lt -m then
          n := d;
          alpha := 2*O.2 - 1;
          g,x,y := ExtendedGreatestCommonDivisor(n^2,-Integers()!Norm(alpha));
          assert g eq n;
          assert x*n^2 - y*Norm(alpha) eq n;
          if d gt 1 then 
            ideals cat:= [<n,alpha,x,y>];
          end if;
        end if;
      end for;
  end case;
  
  return ideals;
end function;



//------------------------------------------------------------------------------

procedure class_group_reps(~class_group_elements, ~elements)
// Given a nonempty list of elements of the maximal order O in an imaginary
// quadratic field, return generators (and extra information) for ideals 
// representing every element of the class group of O. Namely, for every element
// of the class group compute n, alpha, x, y, where 
//      (n,alpha) is an ideal representing the class group element, 
//      n^2 * x - y * Norm(alpha) = n, and
//      o is the order of the element in the class group.
// class_group_elements is assumed to be an empty list.
// elements is a list of elements of O of small norm.

  K := Parent(elements[1]);
  O := MaximalOrder(K);
  Delta := Discriminant(O);
  
  G,phi := ClassGroup(O);
  // G is the class group as an abstract group.
  // phi is a map that takes an element of G to an ideal representing that
  // class
  CGrep := Inverse(phi);
  // CGrep sends an ideal to its class in G.
  
  // We want class group representatives that are small.
  // We will be working with relatively small discriminants, so we do this
  // inefficiently, as we expect it to be a small amount of work compared to 
  // the rest of our algorithm.

  // Our plan: List elements alpha of small norm. For each such alpha,
  // find rational integers n that divide Norm(alpha), that are not
  // divisible by inert primes, and such that GCD(n^2, Norm(alpha)) = n. 
  // Compute the image of the ideal (n,alpha) in the class group, and if we do 
  // not already have a representative for that element, add (n,alpha) to our
  // list.
  
  class_group_elements := [<1, O!0, 1, 0, G!0, 1>];
  taken := [Identity(G)];

  for alpha in elements do
    N := Integers()!Norm(alpha);
    if N gt 1 then
      M := 1;
      for p in PrimeBasis(N) do
        if p eq 2 then
          case Delta mod 8:
            when 1: 
              // 2 is split. 
              M *:= 2^Valuation(N,2);
            when 5: 
            ;
              // 2 is inert. 
            else
              // 2 is ramified.
              M *:= 2;
          end case;
        else
          // p is odd
          case LegendreSymbol(Delta,p):
            when 1:
              M *:= p^Valuation(N,p);
            when 0: 
              M *:= p;
          end case;
        end if;
      end for;
      
      // Let n run through the divisors of M.
      for n in Divisors(M) do
        I := ideal<O | n,alpha>;
        g := CGrep(I);
        if not g in taken then
          gcd,x,y := ExtendedGreatestCommonDivisor(n^2,-Integers()!Norm(alpha));
          if gcd eq n then
            taken cat:= [g];
            class_group_elements cat:= [<n,alpha,x,y,g,Order(g)>];
            if #taken eq #G then
              break alpha;
            end if;
          end if;
        end if;
        // Now obtain the inverse of g with the conjugate ideal
        if not -g in taken then
          gcd,x,y := ExtendedGreatestCommonDivisor(n^2,-Integers()!Norm(alpha));
          if gcd eq n then
            taken cat:= [-g];
            class_group_elements cat:= [<n,Conjugate(alpha),x,y,g,Order(g)>];
            if #taken eq #G then
              break alpha;
            end if;
          end if;
        end if;

      end for;
    end if;
  end for;

end procedure;


//------------------------------------------------------------------------------

/*
The function below uses a speedup based on the fact that the 2-torsion of
the class group acts on the set of principal polarizations of O x O. The action
is as follows:

Given a 2-torsion element represented by an ideal I, and given a polarization
P := [N1, alpha; alphabar, N2], we note that P is also a polarization of I x I.
Since I is 2-torsion, there is an isomorphism O x O --> I x I. Pulling P back
via this isomorphism gives another principal polarization on O x O.

To make this explicit, we use a particular representation of the ideal classes
of order 2. Namely, if our field K is Q(\sqrt{m}) with m squarefree, then every
ideal class of order 2 has a representative ideal I that is stable under complex
conjugation. The function order2() defined above produces such I. (And it is
easy to see that if I is stable under conjugation, then I has order 1 or 2 in
the class group.)

Let I = (n, beta) be an ideal stable under complex conjugation. Let x and y
be integers such that x*n^2 - y*Norm(beta) = n. Then we see that the matrix M
below gives an isomorphism O x O --> I x I:

M = [x*n       beta]
    [y*betabar    n]

Given a polarization 

P = [N1       alpha]
    [alphabar    N2]
    
we see that the pullback of P by M is (1/n) Mstar * P * M, where Mstar is the
conjugate transpose of M. That is, the pullback is

(1/n) [x*n     y*beta] [N1       alpha] [x*n       beta]
      [betabar      n] [alphabar    N2] [y*betabar    n],
      
and we compute that this is equal to

[newN1       newalpha]
[newalphabar    newN2],

where 

   newN1 := x^2*n*N1 + x*y*alpha*betabar + x*y*alphabar*beta + y^2*N2*beta*betabar/n
newalpha := x*n*alpha + x*N1*beta + y*N2*beta + y*alphabar*beta^2/n
   newN2 := n*N2 + alpha*betabar + alphabar*beta + N1*beta*betabar/n.

In the function below, we use this action to get more polarizations from each
on we find by enumeration.
*/

function polarizations(Delta: f := -1, verbose := false, veryverbose := false)
  // "f" indicates whether to use the default upper bound on the size of the
  //      precomputed list of elements of O of given norms.
  // Require that Delta be fundamental.
  // Compute number of polarizations via Hayashida.
  // Enumerate pairs N1, N2, and for each pair, enumerate alpha with N1*N2 - Norm(alpha) = 1.
  // Check to see if we get a reduced polarization.
  // If we do, add to list.
  // Also, add to the list all of the polarizations associated to this one by
  //     action of the two-torsion of the class group.
  // Stop when we have them all.
  // Return the list of polarizations, together with their automorphism groups.
  
  // The variable "elements" will contain a list of all of the elements of O
  // whose norm is less than factor*Delta^2, where "factor" is either set to
  // the value of the optional input "f", or is equal to 0.7*Log(-Delta).
  // The list will be sorted in increasing order of the norm.
  // The variables "starting" and "ending" will have the following properties:
  // For every n < factor*Delta^2 that is a norm, starting[n+1] will be the
  // index of the first element of "elements" that has norm n, and ending[n+1]
  // will be the index of the last element in "elements" that has norm n.
  // If n < factor*Delta^2 is not a norm, then starting[n+1] = ending[n+1] = -1.
  
  // "elements", "starting", and "ending" will be passed to various procedures.
  
  assert IsFundamentalDiscriminant(Delta);
  K := QuadraticField(Delta);
  O<w> := MaximalOrder(K);
  
  if f eq -1 then 
    factor := 0.7*Log(-Delta);
  elif f eq -2 then
      if 0 eq Delta mod 2 then factor := 0.06-0.001*Delta;
      else factor := 0.18-0.0002*Delta; end if;
  else
    factor := f;
  end if;    
  
  bigelements := Ceiling(factor*Delta^2);
  
  elements := [];
  if 0 eq Delta mod 2 then
    m := -(Delta div 4);
    assert O.2^2 eq -m;
    y := 0;
    while m*y^2 lt bigelements do
      x := 0;
      norm := x^2 + m*y^2;
      while norm lt bigelements do
        elements cat:= [z : z in {O![x,y],O![x,-y],O![-x,y],O![-x,-y]}];
        x +:=1;
        norm := x^2 + m*y^2;
      end while;
      y+:=1;
    end while;
  else
    m := -Delta;
    assert (2*O.2 - 1)^2 eq -m;
    y := 0;
    while m*y^2 lt 4*bigelements do
      x := y mod 2;
      norm := x^2 + m*y^2;
      while norm lt 4*bigelements do
        elements cat:= [z : z in {O![(x-y) div 2,y], O![(x+y) div 2,-y], O![(-x-y) div 2,y], O![(-x+y) div 2,-y]}];
        x +:=2;
        norm := x^2 + m*y^2;
      end while;
      y+:=1;
    end while;
  end if;

  normelements := [Norm(a) : a in elements];
  
  ParallelSort(~normelements,~elements);
  
  starting := [-1 : i in [0..bigelements]];
  ending := starting;
  
  n := 0;
  starting[1] := 1;
  for i in [2..#elements] do
    if Norm(elements[i]) ne n then
      ending[n+1] := i-1;
      n := Norm(elements[i]);
      starting[n+1] := i;
    end if;
  end for;
  ending[n+1] := #elements;
  
  if verbose then printf "I have finished computing and sorting all elements of norm less than %o.\n\n",bigelements; end if;
  
  class_group_elements := [];
  class_group_reps(~class_group_elements,~elements);
  torsion := order2(Delta);
  
  goal := HayashidaCountPolarizations(Delta);
  pols := [];
  justpols := [];
  
  if verbose then printf "We are searching for %o polarizations.\n\n", goal; end if;
  
  // First, create the split polarizations.
  
  taken := [];
  for I in class_group_elements do
    n,alpha,x,y,g,o := Explode(I);
    // Ideal is (n,alpha). We have x*n^2 - y*Norm(alpha) = n. And o is the
    // order of the ideal in the class group.
    
    // We have an isomorphism O x O --> I x Ibar given by
    // [ x*n        y*alpha ]
    // [ alphabar   n       ]
    // We pull back the product polarization on the lattice I x I^{-1} via
    // this ismorphism.
    
    // Only use one element from each g, -g pair.
    
    if not g in taken then
      taken cat:= [g,-g];
      cofactor := Integers()!(Norm(alpha)/n);
      N1 := x + (x*y + 1)*cofactor;
      N2 := n + y^2*cofactor;
      beta := (x*y + 1)*alpha;
    
      Q := [N1,N2,beta];
      reduce_polarization(~Q,~elements,~starting,~ending: verbose:=veryverbose);
    
      pols cat:= [<Q, "split">];
      justpols cat:= [Q];
    end if;
  end for;
  
  // Now the nonsplit polarizations. For these, the product of P1 and P2
  // is at least 4.

  product := 3;
  while #pols lt goal do
    product +:= 1;
    for N1 in Divisors(product) do
      N2 := product div N1;
      if N1 le N2 and N1 gt 1 then
        // N1*N2 - Norm(alpha) = 1
        norm := N1*N2 - 1;
        if starting[norm+1] eq -1 then
          alpha_list := [];
        else
          alpha_list := [elements[i] : i in [starting[norm+1]..ending[norm+1]]];
          alpha_list := [a : a in alpha_list | Trace(a) ge 0];
        end if;
        
        for alpha in alpha_list do
          P := [N1, N2, alpha];
          Preduced := true;
          set_reduced_flag(~P,~Preduced,~elements,~starting,~ending);
          if Preduced and not P in justpols then
            pols cat:= [<P,"nonsplit">];
            justpols cat:= [P];
            if verbose then 
              printf "Here is another polarization: %o\n", P;
              printf "We have %o left to find.\n\n", goal-#pols;
            end if;
            // Now let the two-torsion of the class group act.
            alphabar := conjugate(alpha);
            for t in torsion do
              if goal eq #pols then break t; end if;
              n := t[1]; 
              beta := t[2];
              betabar := conjugate(beta);
              x := t[3];
              y := t[4];
              
              TraceABbar := Trace(alpha*betabar);
              NormBovern := Norm(beta)/n;
              BBovern := beta^2/n;

              newN1 := x^2*n*N1 + x*y*TraceABbar + y^2*N2*NormBovern;
              newalpha := x*n*alpha + x*N1*beta + y*N2*beta + y*alphabar*BBovern;
              newN2 := NormBovern*N1 + TraceABbar + n*N2;

              newN1 := Integers()!newN1;
              newN2 := Integers()!newN2;
              newalpha := O!newalpha;

              if verbose then printf "Working to reduce %o ...\n", [newN1,newN2,newalpha]; end if;
              Q := [newN1,newN2,newalpha];
              reduce_polarization(~Q,~elements,~starting,~ending: verbose:=veryverbose);
              if not Q in justpols then
                pols cat:= [<Q,"nonsplit">];
                justpols cat:= [Q];
                if verbose then 
                  printf "Here is another polarization: %o\n", Q;
                  printf "We have %o left to find.\n\n", goal-#pols;
                end if;
              end if;
            end for;
            if #pols eq goal then 
              break N1;
            end if;
          end if;
        end for;
      end if;
    end for;
  end while;
  
  Sort(~pols);
  answer := [];
  for P in pols do
    Q := P[1];
    Pautos := [];
    compute_automorphisms(~Q,~elements,~starting,~ending,~Pautos);
    answer cat:= [<P[1], P[2], Pautos>];
  end for;
 
  return answer;
      
end function;


//------------------------------------------------------------------------------

function VerifyPaperStatements()
  // This function verifies the statements in [GélinHoweRitzenthaler2019]
  // concerning the number of isomorphism classes of nonsplit principally
  // polarized surfaces of the form E x E, where E has CM by a quadratic maximal
  // order with class group of exponent 2. The function returns a boolean and
  // a list of polarizations. The boolean says whether the number of nonsplit
  // polarizations matches what is stated in Table 2 of the paper, and the list
  // of polarizations give the polarization matrix, a string that is either 
  // "split" or "nonsplit", and the automorphism group of the polarizations.
  // The function also prints out the polarization, the split status, and the
  // size of the automorphism group.

  // The following variable contains the list of discriminants of quadratic 
  // maximal orders with class groups of exponent 2 and (Z/2Z)-rank 0, 1, 2, 3,
  // and 4. (No higher-rank examples exist.)
  
  DeltaLists := [
                 [ -163, -67, -43, -19, -11, -8, -7],
                 [ -427, -403, -267, -235, -232, -187, -148, -123, -115, -91, -88, -52, -51, -40, -35, -24, -20, -15 ],
                 [ -1435, -1012, -795, -760, -715, -708, -627, -595, -555, -532, -520, -483, -435, -408, -372, -340, -312, -280, -228, -195, -168, -132, -120, -84 ],
                 [ -3315, -3003, -1995, -1848, -1540, -1428, -1380, -1320, -1155, -1092, -840, -660, -420 ],
                 [ -5460 ]
                ];

  PaperClaims := AssociativeArray();

  discs  := [-7,-8,-11,-19,-43,-67,-163,-15,-20,-24,-35,-40,-51,-52,-88,-91,-115,-123,-148,-187,-232,-235,-267,-403,-427,-84,-120,-132,-168,-195,-228,-280,-312,-340,-372,-408,-435,-483,-520,-532,-555,-595,-627,-708,-715,-760,-795,-1012,-1435,-420,-660,-840,-1092,-1155,-1320,-1380,-1428,-1540,-1848,-1995,-3003,-3315,-5460];
  counts := [0,1,1,1,2,3,7,0,1,1,2,2,2,2,4,4,6,4,5,8,9,12,8,18,16,2,5,3,4,8,5,14,11,14,8,14,16,12,25,14,20,28,16,15,36,41,28,28,64,10,16,22,22,32,36,34,28,46,46,56,72,128,128];

  bool := Set(&cat DeltaLists) eq Set(discs);

  for i in [1..#discs] do
    PaperClaims[discs[i]] := counts[i];
  end for;

  PolarizationLists := <>;

  h := 1; 
  time for Deltas in DeltaLists do
    printf "Discriminants with class number %o\n", h;
    if h le 8 then 
      print "================================="; 
    else 
      print "=================================="; 
    end if;

    Polars := <>;
    for D in Deltas do
      time pols := polarizations(D : f:=Log(-D));
      bool and:= (PaperClaims[D] eq #[p : p in pols | p[2] eq "nonsplit"]);
      assert bool;
      Polars cat:= <<pols>>;
      printf "Delta := %o\n", D;
      for a in pols do printf "%o, %o, %o\n", a[1], a[2], #a[3]; end for;
      print "";
    end for;
    PolarizationLists cat:= <Polars>;
    h := h * 2;
  end for;

  return bool, PolarizationLists;
end function;
