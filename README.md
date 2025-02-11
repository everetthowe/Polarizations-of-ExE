# Polarizations-of-ExE
Magma routines for computing principal polarizations of squares of elliptic curves with CM by a maximal order.

This collection of Magma routines is associated with the paper
“Principally polarized squares of elliptic curves with field of moduli equal to Q”
by Alexander Gélin, Everett W. Howe, and Christophe Ritzenthaler
[GélinHoweRitzenthaler2019].

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

