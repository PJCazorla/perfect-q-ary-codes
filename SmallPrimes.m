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
**              The algorithm used to solve the equation is taken 
**              from the following paper:
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
*******************************************************************/

/******************************************************
** Name: solveMordellEquation
** Description: This function solves the Mordell equation
**                  y^2 = x^3 + a,
**              where x and y are S-integers, where S is 
**              a finite set of rational primes. The implementation here
**              is based upon Algorithm 4.2 in the paper 
**              
**              R. von Kanel and B. Matschke, "Solving S-unit, Mordell, Thue, 
**              Thue–Mahler and Generalized Ramanujan–Nagell Equations via the 
**              Shimura–Taniyama Conjecture", Memoirs of the AMS, 2016
**              for values of p which are not too large and makes use of the 
**              in-built Magma function otherwise.
**
** Arguments: primes -> List of primes which are allowed to be in the denominator.
**            a -> Coefficient of the Mordell equation.
**
** Output: Solutions (x,y) of the Mordell equation which are S-integers.
******************************************************/
function solveMordellEquation(primes, a)

	solutions := {};
	
	/* We compute the bound aS in the paper */
	aS := 1728*(&*primes)^2;
	for p in PrimeDivisors(a) do
		if Valuation(a, p) eq 1 then
			aS *:= p;
		else
			aS *:= p^2;
		end if;
	end for;
	
	/* If this is too large, the computation via modular symbols IsEven
	   impractical and the elliptic curves are not in Cremona's database, 
	   so we compute them directly via S-integral points. */
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

		pts := SIntegralPoints(E, primes : FBasis := gens);

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
						
					if Set(PrimeDivisors(Denominator(x))) diff primes eq {} and Set(PrimeDivisors(Denominator(y))) diff primes eq {} then 
						solutions := solutions join {[x, y]};
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
**              where y is a S-unit, that is, a rational number supported
**              only on primes of a finite set S, and x is a S-integer.
**             
**              This is stronger than condition (c) in the theorem since 
**              the equation Cw^2 + 1 = q^gamma * 2^m can be written As
**                (Cw)^2 + C = C q^gamma * 2^m,
**              and it is therefore sufficient to solve this equation with 
**              b = c = C and S = {gamma,m}.
**              
**              The implementation here is based upon algorithm 6.1 in 
**              
**              R. von Kanel and B. Matschke, "Solving S-unit, Mordell, Thue, 
**              Thue–Mahler and Generalized Ramanujan–Nagell Equations via the 
**              Shimura–Taniyama Conjecture", Memoirs of the AMS, 2016
**
**              and makes use of the above function to solve Mordell equation.
**
** Arguments: b, c -> Coefficients of the above equation.
**            primes -> Finite list of primes where y is supported.
**
** Output: Solutions (x,y) on O x O^*, where O is the ring of S-integers.
******************************************************/
function solveRamanujanNagell(b, c, primes)

	solutions := {};
	
	/* The algorithm requires to solve several Mordell equations,
	   one for each divisor of the product of primes squared. */
	for e in Divisors((&*primes)^2) do 
	
		Ya, solved := solveMordellEquation(primes, -b*(e*c)^2);
		
		if not solved then 
			return {}, false;
		end if;
		
		/* For each solution of the Mordell equation, we reconstruct
		   the associated solution of the Ramanujan–Nagell equation */
		for solution in Ya do 
			u := solution[1];
			v := solution[2];
			
			x := v/(e*c);
			y := u^3/(e^2*c^3);
			
			if (x^2 + b) eq c*y then 
				solutions := solutions join {[Abs(x), y]};
			end if;
		
		end for;
	
	end for;
	
	return solutions, true;

end function;

function LloydsTheorem (q, n, M : verbose := true)

	P<x> := PolynomialRing(Integers());
	
	if verbose then 
		print "Applying Lloyd's theorem to the possible code with q=", q, " and n=", n;
	end if;
	
	Lt := (q-1)^2*(n-x)*(n-x-1) - 2*(q-1)*(x-1)*(n-x) + (x-1)*(x-2);
	
	roots := Roots(Lt);
	
	if #roots eq 2 and 1 le roots[1, 1] and roots[1, 1] le n and 1 le roots[2, 1] and roots[2, 1] le n then 
		if verbose then 
			print "Lloyd's theorem was unsuccessful.";
		end if;
		return false;
	end if;
	
	if verbose then 
		print "Lloyd's theorem was successful.";
	end if;
	
	return true;

end function;

function ruleOut(q : verbose := true)

	possibleCodes := {};
	
	print "----------------------------------";
	print "Considering case q = ", q;
	
	if IsEven(q) then 
		solutions, solved := solveRamanujanNagell(8-(3-q)^2, 8, Set(PrimeDivisors(q)));
		
		if verbose then 
			print "Solving Ramanujan–-Nagell equation";
		end if;
	else 	
		if (q mod 16) eq 9 or (q mod 16) eq 13 then 
			if verbose then 
				print "It is not necessary to solve the Ramanujan-–Nagell equations due to congruence conditions";
			end if;
			return {};
		else
			solutions, solved := solveRamanujanNagell(2-((3-q)^2 div 4), 2, Set(PrimeDivisors(q)));
			
			if verbose then 
				print "Solving Ramanujan-–Nagell equation";
			end if;
		end if;
	end if;

	if not solved then 
		print "Problems when resolving the Lebesgue--Nagell equation. An alternative method is required.";
		print "----------------------------------";
		return {}, false;
	end if;
	
	for sol in solutions do
		x := sol[1];
		y := sol[2];
		
		if IsIntegral(x) and IsIntegral(y) then
			
			x := Integers()!x;
			y := Integers()!y;
			
			if IsEven(q) then 
				n := (x+q-3)/(2*(q-1));
			else
				n := (2*x+q-3)/(2*(q-1));
			end if;
			
			if n gt 2 and IsIntegral(n) and IsIntegral(q^n/y) then 
				
				n := Integers()!n;
				M := Integers()!q^n/y;
				
				if verbose then 
					print "There is a possible code with q=", q, " and n=", n;
				end if;
				
				if not LloydsTheorem(q, n, M : verbose := verbose) then 
					possibleCodes := possibleCodes join {[n, M, 5]};
				end if;
				
			end if;
		end if;
		
	end for;
	
	print "----------------------------------";
	return possibleCodes, true;

end function;

for q in [x : x in [2..2000] | not IsPrimePower(x) and (Set(PrimeDivisors(x)) diff {2,3,5,7,11}) eq {} ] do 
	ruleOut(q);
end for;

