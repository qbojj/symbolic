CelineRec := proc(F, S, n, k)
    # Celine's method for hypergeometric sums.
    # F is the summand, S is the sum, n is the main variable, and k is the summation variable.
    # Returns a recurrence relation for S in terms of n.
    local maxI, maxJ, d, II, JJ, i, j;

    maxI := 5;
    maxJ := 5;

    # sum_{i=0}{I}{sum_{j=0}{J}{coeffs[i, j] * F(n + i, k + j)/F(n, k)}} = 0

    local funcs, coeffs;
    funcs := (i, j) -> simplify(convert(subs(n=n+i, k=k+j, F)/F, factorial));
    coeffs := array(0..maxI, 0..maxJ);

    for II from 1 to maxI do
        for JJ from 0 to maxJ do
            # check if we can solve for coeffs[0..I, 0..J] such as those are independent of k
            local poly_eq;

            poly_eq := simplify(sum(sum(coeffs[i, j] * funcs(i, j), i=0..II), j=0..JJ));

            # equate the nominator to zero k-polynomial
            local nominator, eqs;
            nominator := convert(expand(numer(poly_eq)), polynom);
            eqs := [seq(coeff(nominator, k, d) = 0, d=0..degree(nominator, k))];

            # try to solve for coeffs[0..I, 0..J] - must be nontrivial
            local sol, nontrivial;
            nontrivial := sum(sum(coeffs[i, j]^2, j=0..JJ), i=0..II) <> 0;
            sol := solve([op(eqs), nontrivial], {seq(seq(coeffs[i, j], i=0..II), j=0..JJ)});

            if sol <> NULL then
                # print(cat("Found a solution for I=", II, " and J=", JJ, ": ", sol));
                # found a solution - now we can build the recurrence relation for S, by summing over all k
                local rec;
                rec := subs(sol, sum(simplify(sum(coeffs[i, j], j=0..JJ) * S(n + i)), i=0..II));
                # rec := simplify(numer(simplify(rec)));

                # check if nontrivial
                if evalb(simplify(rec) <> 0) then
                    return simplify(rec) = 0;
                fi;
            fi;
        od;
    od;

    error "Celine's method failed to find a recurrence relation with the given bounds.";
end proc:
