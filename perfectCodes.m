/*************************************************
** MODULE NAME: perfectCodes.m
** Author: Pedro-Jose Cazorla Garcia
** Affiliation: University of Manchester, UK.
** Description: This module includes functions to disprove the 
**              existence of perfect (n, M, d) codes with Hamming
**              distance 5 (i.e. perfect 2-error correcting codes)
**              over an arbitrary q-adic alphabet, where q is not 
**              necessarily a prime power.
**
**              For this purpose, we explicitly resolve the 
**              Diophantine equation coming from the Hamming bound
**              by reducing it to a Ramanujan-–Nagell type equation.
**
**              The algorithm used to solve the equation is adapted from 
**              Algorithm 4.2 in the following paper:
**                R. von Kanel and B. Matschke, "Solving S-unit, Mordell, Thue, 
**              Thue–Mahler and Generalized Ramanujan–Nagell Equations via the 
**              Shimura–Taniyama Conjecture", Memoirs of the AMS, 2016
**
**              If some solutions exist, we use Lloyd's theorem to prove 
**              that they do not constitute a perfect code.
**
**************************************************/

/*******************************************************************
***** Auxiliary functions - used to solve Mordell equations ********
*****              and to compute cubefree part of integers ********
*******************************************************************/

/******************************************************
** Name: cubeFree
** Description: Given a integer n, this function decomposes it 
**              as n = n0*n1^3, where n0 is cubefree.
**               
** Arguments: n -> The number whose cubefree decomposition we 
**                 want to find.
**
** Output: Solutions (x,y) of the Mordell equation which are S-integers, along with 
**         a boolean value indicating whether the equation has been successfully 
**         solved or not.
******************************************************/

function cubeFree(n) 

	fact := Factorisation(n);
	
	n0 := 1;
	
	/* In order to compute n0, we disregard all cubes in the
	   factorisation of n. */
	for f in fact do
		n0 *:= f[1]^(f[2] mod 3);
	end for;
	
	return n0, Integers()!((n/n0)^(1/3));

end function;

/******************************************************
** Name: solveMordellEquation
** Description: This function solves the Mordell equation
**                  y^2 = x^3 + a,
**              where x and y are integers. The implementation here
**              is based upon Algorithm 4.2 in the paper 
**              
**              R. von Kanel and B. Matschke, "Solving S-unit, Mordell, Thue, 
**              Thue–Mahler and Generalized Ramanujan–Nagell Equations via the 
**              Shimura–Taniyama Conjecture", Memoirs of the AMS, 2016,
**
**              for values of a which are not too large and makes use of the 
**              in-built Magma function otherwise, with some optimisations
**
** Arguments: a -> Coefficient of the Mordell equation.
**
** Output: Solutions (x,y) of the Mordell equation which are integers, along with 
**         a boolean value indicating whether the equation has been successfully 
**         solved or not.
******************************************************/
function solveMordellEquation(a)

	solutions := {};
	
	/* We compute the bound aS in the paper. Note that we do not require
       S-integers so the set S is empty and the bound is smaller.	*/
	aS := 1728;
	for p in PrimeDivisors(a) do
		if Valuation(a, p) eq 1 then
			aS *:= p;
		else
			aS *:= p^2;
		end if;
	end for;
	
	/* If this is too large, the computation via modular symbols is
	   impractical and the elliptic curves are not in Cremona's database, 
	   so we compute them directly via integral points. */
	if aS ge 500000 then 
	
		/* The computation is often improved by precomputing generators. 
	           We attempt to do so in generality. */
		E := EllipticCurve([0,0,0,0,a]);

		gens, found1, found2 := Generators(E);

		/* If we are unable to find them, in many cases it is due to the 
           fact that we cannot precisely determine the rank algebraically.
           Since BSD is true for ranks 0 and 1, we can try to optimise 
           these cases */
		if not found1 or not found2 then
			rAn, coeff := AnalyticRank(E);

			/* If the analytic rank is 0, there are no generators to compute */
			if rAn eq 0 then 
				gens := [Identity(E)];
			end if;

			/* If the rank is 1, we could find a generator 
		   	by looking for Heegner points. */
			if rAn eq 1 then 
				found, P := HeegnerPoint(E);
			
				if found then 
					gens := [P];
				else
					print "Unable to compute Heegner points for the curve ", E;
					return [], false;
				end if;
		
			end if;

			/* If the analytic rank (and hence the algebraic rank) is greater than 
                           1, there are no further tricks and we cannot compute the generators */
			if rAn gt 1 then
				print "Unable to compute generators for the curve ", E;
				return [], false;
			end if;
		end if;

		pts := IntegralPoints(E: FBasis := gens);

		for point in pts do
			solutions := solutions join {[point[1], point[2]]};
		end for;
		
		return solutions, true;
	end if;
	
	/* Otherwise, all curves that we need are previously computed 
	   in Cremona's database, and we simply look them up */
	db := CremonaDatabase();
	
	for N in Divisors(aS) do
		nClasses := NumberOfIsogenyClasses(db, N);
		for i in [1..nClasses] do
			nCurves := NumberOfCurves(db, N, i);
			for j in [1..nCurves] do

				/* For every elliptic curve, we check if their invariants (c4, c6) 
				   satisfy the necessary conditions */
				E := EllipticCurve(db, N, i, j);
					
				invs := cInvariants(E);
				q := Abs((invs[1]^3- invs[2]^2)/a);
					
				m := Numerator(q);
				n := Denominator(q);
					
				mPower, u1 := IsPower(m, 12);
				nPower, u2 := IsPower(n, 12);
					
				if mPower and nPower then 
					u := u1/u2;
					x := invs[1]/u^4;
					y := invs[2]/u^6;
						
					if IsIntegral(x) and IsIntegral(y) then 
						solutions := solutions join {[Integers()!x, Integers()!y]};
					end if;
						
				end if;

			end for;
		end for;
	end for;

	return solutions, true;

end function;

/*******************************************************************
************************ Main functions ****************************
*******************************************************************/

/******************************************************
** Name: solveRamanujanNagell
** Description: This function solves the Ramanujan–Nagell equation
**                  x^2 + b = cy,
**              where y is supported only on a finite list of primes,
**              and x is a integer.
**              
**              The implementation here reduces the computation to 
**              computing integral points in certain Mordell curves.
**              and makes use of the above function to solve Mordell equation.
**
** Arguments: b, c -> Coefficients of the above equation.
**            primes -> Finite list of primes where y is supported.
**
** Output: Solutions (x,y) on Z x Z, where y is supported only on the primes specified, along with 
**         a boolean value indicating whether it has been successfully solved or not.
******************************************************/
function solveRamanujanNagell(b, c, primes)

	solutions := {};
	
	/* We can get slightly more efficient results if we assume that 
	   gcd(c, y) = 1. We can do so by absorbing all primes into y 
	   and changing c appropiately. In order to recover the solutions
	   to the original equation, we keep track of the old value of c. */
	   
	cOld := c;
	
	for p in primes do
		c := c div p^Valuation(c, p);
	end for;
	
	c0, c1 := cubeFree(c);
	
	/* The algorithm requires to solve several Mordell equations,
	   one for each divisor of the product of primes squared. */
	for e in Divisors((&*primes)^2) do 
	
		Ya, solved := solveMordellEquation(-b*(e*c0)^2);
		
		if not solved then 
			return {}, false;
		end if;
		
		/* For each solution of the Mordell equation, we reconstruct
		   the associated solution of the Ramanujan–Nagell equation */
		for solution in Ya do 
			u := solution[1];
			v := solution[2];
			
			x := v/(e*c0);
			y := u^3/(c*e^2*c0^2);

			if IsIntegral(x) and IsIntegral(y) and (x^2 + b) eq c*y then 
				solutions := solutions join {[Abs(x), cOld*y/c]};
			end if;
		
		end for;
	
	end for;
	
	return solutions, true;

end function;

/******************************************************
** Name: LloydsTheorem 
** Description: This function applies Lloyd's theorem to disprove 
**              the existence of a 2-error correcting perfect code 
**              for a given value of n and M, over a q-ary alphabet.
**
** Arguments: q -> Size of the alphabet.
**            n, M -> Length of the words and number of words in the code.
**
** Parameters: verbose -> Displays additional information about the computation.
**
** Output: True if the code is proved to not be perfect. False otherwise.
******************************************************/
function LloydsTheorem (q, n, M : verbose := true)

	P<x> := PolynomialRing(Integers());
	
	if verbose then 
		print "Applying Lloyd's theorem to the possible code with q=", q, " and n=", n;
	end if;
	
	/* We build the Lloyd's polynomial. By Lloyd's theorem, it must have two
	   integer roots in [1,n], so we compute all integer roots. */
	Lt := (q-1)^2*(n-x)*(n-x-1) - 2*(q-1)*(x-1)*(n-x) + (x-1)*(x-2);
	roots := Roots(Lt);
	
	/* If there are precisely two integer roots in the range, the code could be perfect. */
	if #roots eq 2 and 1 le roots[1, 1] and roots[1, 1] le n and 1 le roots[2, 1] and roots[2, 1] le n then 
		if verbose then 
			print "Lloyd's theorem was unsuccessful.";
		end if;
		return false;
	end if;
	
	if verbose then 
		print "Lloyd's theorem was successful.";
	end if;
	
	/* Otherwise, the code is definitely not perfect. */
	return true;

end function;

/******************************************************
** Name: ruleOut 
** Description: This function attempts to disprove the existence of a 
**              perfect code over a q-ary alphabet by showing that there 
**              are no solutions to the sphere-packing equation which 
**              furthermore satisfy Lloyd's theorem. Note that this 
**              function applies for an arbitrary value of q (prime power 
**              or non-prime power).
**
** Arguments: q -> Size of the alphabet.
**
** Parameters: verbose -> Displays additional information about the computation.
**
** Output: The possible perfect codes, along with the boolean value true if the function 
**         is computationally successful.
**         False if it is not.
******************************************************/
function ruleOut(q : verbose := true)

	possibleCodes := {};
	
	/* Firstly, we need to solve the Ramanujan-–Nagell equations arising from the 
	   sphere packing bound. They are slightly different depending on whether q 
	   is even or not. */
	print "----------------------------------";
	print "Considering case q = ", q;
	
	/* If q is even, the equation is given by 
		x^2 + (8-(q-3)^2) = 8y,
	   where y is supported only on primes dividing q. */
	if IsEven(q) then 
		solutions, solved := solveRamanujanNagell(8-(3-q)^2, 8, Set(PrimeDivisors(q)));
		
		if verbose then 
			print "Solving Ramanujan–-Nagell equation";
		end if;
	else 	
		
		/* If q is odd, the equation is given by 
			x^2 + (2-((q-3)/2)^2) = 2y,
		   where y is supported only on primes dividing q. */
		solutions, solved := solveRamanujanNagell(2-((3-q)^2 div 4), 2, Set(PrimeDivisors(q)));
			
		if verbose then 
			print "Solving Ramanujan-–Nagell equation";
		end if;
	end if;

	/* If q is too large or is supported on too many primes, we may be unable to resolve the equation. 
	   In this case, we simply inform the user. */
	if not solved then 
		print "Problems when resolving the Ramanujan--Nagell equation. An alternative method is required.";
		print "----------------------------------";
		return {}, false;
	end if;
	
	/* For every solution (x,y) of the aforementioned Ramanujan--Nagell equation, we need to reconstruct 
	   the values of n and M in the perfect code. */
	for sol in solutions do
		x := sol[1];
		y := sol[2];
		
		/* Since our resolution of the Ramanujan--Nagell equation could give fractional values for x 
		   and y, we only consider those values which are integers. */
		if IsIntegral(x) and IsIntegral(y) then
			
			x := Integers()!x;
			y := Integers()!y;
			
			/* If q is even, we know that 
				x = 2n(q-1) + 3-q.
			   If q is odd, then the corresponding formula is 
			    2x = 2n(q-1) + 3-q,
			   since the equation has been transformed.
			*/
			
			if IsEven(q) then 
				n := (x+q-3)/(2*(q-1));
			else
				n := (2*x+q-3)/(2*(q-1));
			end if;
			
			/* We rule out the case n = 2, to avoid trivial solutions. Then, 
			   it is elementary to recover the value of M, since we have that 
			   M = q^n/y */
			if n gt 2 and IsIntegral(n) and IsIntegral(q^n/y) then 
				
				n := Integers()!n;
				M := Integers()!q^n/y;
				
				if verbose then 
					print "There is a possible code with q=", q, " and n=", n;
				end if;
				
				/* Since there is a possible (n, M, 5) code, we try to rule it 
				   out by applying Lloyd's Theorem .*/
				if not LloydsTheorem(q, n, M : verbose := verbose) then 
					possibleCodes := possibleCodes join {[n, M, 5]};
				end if;
				
			end if;
		end if;
		
	end for;
	
	print "----------------------------------";
	return possibleCodes, true;

end function;

/********************************
** SANITY CHECK                 */
/*
for q in [x : x in [2..70]] do 
	ruleOut(q);
end for;
*/
/********************************/

