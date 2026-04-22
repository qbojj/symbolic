HGTerm := proc(top::list, bottom::list, z, k::name)
    local num, den, i;
    num := 1;
    den := 1;

    for i from 1 to nops(top) do
        num := num * pochhammer(top[i], k);
    od;

    for i from 1 to nops(bottom) do
        den := den * pochhammer(bottom[i], k);
    od;

    return simplify(num * z^k / (den * k!));
end proc:

_Eq := proc(x, y)
    return evalb(simplify(x - y) = 0);
end proc:

_RemoveListEntry := proc(L::list, idx::posint)
    if nops(L) = 1 then
        return [];
    elif idx = 1 then
        return [op(2..nops(L), L)];
    elif idx = nops(L) then
        return [op(1..nops(L)-1, L)];
    else
        return [op(1..idx-1, L), op(idx+1..nops(L), L)];
    fi;
end proc:

_IsNegatedExpr := proc(x)
    return type(x, nonposint) or StringTools:-IsPrefix("-", convert(x, string));
end proc:

# Parse a polynomial in k as const * Product_i (k + alpha_i), returning
# [const, [alpha_1, ..., alpha_m]]. Returns FAIL for non-linear factors.
_ParseLinearFactors := proc(poly, k::name)
    local fac, c0, i, f, e, ck, d0, alpha, params, j;

    fac := factors(expand(poly));
    c0 := fac[1];
    params := [];

    for i from 1 to nops(fac[2]) do
        f := fac[2][i][1];
        e := fac[2][i][2];

        if degree(f, k) = 0 then
            c0 := c0 * f^e;
        elif degree(f, k) = 1 then
            ck := coeff(f, k, 1);
            d0 := subs(k = 0, f);
            alpha := simplify(d0 / ck);
            c0 := c0 * ck^e;

            for j from 1 to e do
                params := [op(params), alpha];
            od;
        else
            return FAIL;
        fi;
    od;

    return [simplify(c0), params];
end proc:

# Recover [cfac, top, bottom, z] from a hypergeometric term t_k.
# t_k must satisfy t_{k+1}/t_k = z * Prod(k+a_i) / ((k+1)*Prod(k+b_i)).
_TermToHG := proc(tk, k::name)
    local cfac, ratio, rr, pn, pd, numInfo, denInfo, z, top, bottom;

    cfac := simplify(subs(k = 0, tk));
    if cfac = 0 then
        return FAIL;
    fi;

    ratio := simplify(subs(k = k + 1, tk) / tk);

    # Force pochhammer(a,k+1) -> (a+k)*pochhammer(a,k), then cancel.
    ratio := simplify(subsindets(ratio, specfunc(anything, pochhammer),
        proc(p)
            if _Eq(op(2, p), k + 1) then
                return (op(1, p) + k) * pochhammer(op(1, p), k);
            fi;
            return p;
        end proc));

    rr := simplify(ratio * (k + 1));

    pn := numer(rr);
    pd := denom(rr);

    numInfo := _ParseLinearFactors(pn, k);
    denInfo := _ParseLinearFactors(pd, k);

    if numInfo = FAIL or denInfo = FAIL then
        return FAIL;
    fi;

    z := simplify(numInfo[1] / denInfo[1]);
    top := numInfo[2];
    bottom := denInfo[2];

    return [cfac, top, bottom, z];
end proc:

_CancelCommonParams := proc(top::list, bottom::list)
    local top2, bottom2, changed, i, j;

    top2 := [op(top)];
    bottom2 := [op(bottom)];
    changed := true;

    while changed do
        changed := false;

        for i from 1 to nops(top2) do
            for j from 1 to nops(bottom2) do
                if _Eq(top2[i], bottom2[j]) then
                    top2 := _RemoveListEntry(top2, i);
                    bottom2 := _RemoveListEntry(bottom2, j);
                    changed := true;
                    break;
                fi;
            od;

            if changed then
                break;
            fi;
        od;
    od;

    return top2, bottom2;
end proc:

# Returns FAIL when no rule matches.
ApplyHGIdentity := proc(top::list, bottom::list, z)
    local top2, bottom2, a, b, c, d, e, n, i, j, others, val;

    top2, bottom2 := _CancelCommonParams(top, bottom);

    # 0F0.
    if nops(top2) = 0 and nops(bottom2) = 0 then
        return exp(z);
    fi;

    # 1F0.
    if nops(top2) = 1 and nops(bottom2) = 0 then
        a := top2[1];
        return simplify((1 - z)^(-a), symbolic);
    fi;

    # 2F1 forms.
    if nops(top2) = 2 and nops(bottom2) = 1 then
        a := top2[1];
        b := top2[2];
        c := bottom2[1];

        if _Eq(z, 1) then
            if _IsNegatedExpr(a) then
                n := -a;
                return simplify(pochhammer(c - b, n) / pochhammer(c, n));
            fi;

            if _IsNegatedExpr(b) then
                n := -b;
                return simplify(pochhammer(c - a, n) / pochhammer(c, n));
            fi;

            # Gauss formula: guard against Gamma singularities.
            if not (_IsNegatedExpr(c) or _IsNegatedExpr(c - a - b) or _IsNegatedExpr(c - a) or _IsNegatedExpr(c - b)) then
                return simplify(GAMMA(c) * GAMMA(c - a - b) / (GAMMA(c - a) * GAMMA(c - b)));
            fi;
        fi;

        if _Eq(z, -1) then
            # Pfaff reduction: 2F1(a,b;c;-1) -> 2^(-a) 2F1(a,c-b;c;1/2).
            # This is tried first so z = -1 can reuse the z = 1/2 branch.
            # Guard against Gamma singularities: don't recurse if it would create singularities.
            if not (_IsNegatedExpr(a) or _IsNegatedExpr(c - b)) then
                val := ApplyHGIdentity([a, c - b], [c], 1/2);
                if val <> FAIL then
                    return simplify(2^(-a) * val);
                fi;
            fi;

            if not (_IsNegatedExpr(b) or _IsNegatedExpr(c - a)) then
                val := ApplyHGIdentity([b, c - a], [c], 1/2);
                if val <> FAIL then
                    return simplify(2^(-b) * val);
                fi;
            fi;

            # Direct Kummer identities as fallback: guard against Gamma singularities.
            if _Eq(c, 1 + a - b) then
                if not (_IsNegatedExpr(a/2) or _IsNegatedExpr(1 + a/2 - b)) then
                    return simplify(2^(-a) * GAMMA(1 + a - b) * GAMMA(1 + a/2) /
                        (GAMMA(1 + a) * GAMMA(1 + a/2 - b)));
                fi;
            fi;

            if _Eq(c, 1 + b - a) then
                if not (_IsNegatedExpr(b/2) or _IsNegatedExpr(1 + b/2 - a)) then
                    return simplify(2^(-b) * GAMMA(1 + b - a) * GAMMA(1 + b/2) /
                        (GAMMA(1 + b) * GAMMA(1 + b/2 - a)));
                fi;
            fi;
        fi;

        if _Eq(z, 1/2) then
            if _Eq(b, 1 - a) then
                if not (_IsNegatedExpr(c) or _IsNegatedExpr((a + c) / 2) or _IsNegatedExpr((c - a + 1) / 2)) then
                    return simplify(2^(1 - c) * sqrt(Pi) * GAMMA(c) /
                        (GAMMA((a + c) / 2) * GAMMA((c - a + 1) / 2)));
                fi;
            fi;

            if _Eq(a, 1 - b) then
                if not (_IsNegatedExpr(c) or _IsNegatedExpr((b + c) / 2) or _IsNegatedExpr((c - b + 1) / 2)) then
                    return simplify(2^(1 - c) * sqrt(Pi) * GAMMA(c) /
                        (GAMMA((b + c) / 2) * GAMMA((c - b + 1) / 2)));
                fi;
            fi;
        fi;

        if _Eq(z, 2) then
            # Inversion-based reduction: try to evaluate the 1/z-transformed terms
            # at 1/2. This is useful when the transformed parameters collapse to
            # one of the known database entries.
            # Guard against Gamma singularities: don't use if (b-a) or (c-a) is a non-positive integer.
            if not (_IsNegatedExpr(b - a) or _IsNegatedExpr(c - a)) then
                val := ApplyHGIdentity([a, 1 - c + a], [1 - b + a], 1/2);
                if val <> FAIL then
                    return simplify(GAMMA(c) * GAMMA(b - a) * (-2)^(-a) * val /
                        (GAMMA(b) * GAMMA(c - a)));
                fi;
            fi;

            if not (_IsNegatedExpr(a - b) or _IsNegatedExpr(c - b)) then
                val := ApplyHGIdentity([b, 1 - c + b], [1 - a + b], 1/2);
                if val <> FAIL then
                    return simplify(GAMMA(c) * GAMMA(a - b) * (-2)^(-b) * val /
                        (GAMMA(a) * GAMMA(c - b)));
                fi;
            fi;
        fi;
    fi;

    # Pfaff-Saalschutz.
    if nops(top2) = 3 and nops(bottom2) = 2 and _Eq(z, 1) then
        for i from 1 to 3 do
            if _IsNegatedExpr(top2[i]) then
                n := -top2[i];
                others := _RemoveListEntry(top2, i);
                a := others[1];
                b := others[2];

                for j from 1 to 2 do
                    c := bottom2[j];
                    d := bottom2[3 - j];

                    if _Eq(d, 1 + a + b - c - n) then
                        return simplify(pochhammer(c - a, n) * pochhammer(c - b, n) /
                            (pochhammer(c, n) * pochhammer(c - a - b, n)));
                    fi;
                od;
            fi;
        od;
    fi;

    # Dixon.
    if nops(top2) = 3 and nops(bottom2) = 2 and _Eq(z, 1) then
        for i from 1 to 3 do
            a := top2[i];
            others := _RemoveListEntry(top2, i);
            b := others[1];
            c := others[2];

            if (_Eq(bottom2[1], 1 + a - b) and _Eq(bottom2[2], 1 + a - c)) or
               (_Eq(bottom2[2], 1 + a - b) and _Eq(bottom2[1], 1 + a - c)) then
                return simplify(GAMMA(1 + a/2) * GAMMA(1 + a - b) * GAMMA(1 + a - c) *
                    GAMMA(1 + a/2 - b - c) /
                    (GAMMA(1 + a) * GAMMA(1 + a/2 - b) * GAMMA(1 + a/2 - c) * GAMMA(1 + a - b - c)));
            fi;
        od;
    fi;

    # Watson.
    if nops(top2) = 3 and nops(bottom2) = 2 and _Eq(z, 1) then
        for i from 1 to 3 do
            c := top2[i];
            others := _RemoveListEntry(top2, i);
            a := others[1];
            b := others[2];

            if (_Eq(bottom2[1], (a + b + 1) / 2) and _Eq(bottom2[2], 2 * c)) or
               (_Eq(bottom2[2], (a + b + 1) / 2) and _Eq(bottom2[1], 2 * c)) then
                return simplify(sqrt(Pi) * GAMMA(c + 1/2) * GAMMA((a + b + 1) / 2) *
                    GAMMA(c + (1 - a - b) / 2) /
                    (GAMMA((a + 1) / 2) * GAMMA((b + 1) / 2) *
                     GAMMA(c + (1 - a) / 2) * GAMMA(c + (1 - b) / 2)));
            fi;
        od;
    fi;

    # Whipple.
    if nops(top2) = 3 and nops(bottom2) = 2 and _Eq(z, 1) then
        for i from 1 to 3 do
            a := top2[i];
            for j from 1 to 3 do
                if j <> i and _Eq(top2[j], 1 - a) then
                    if i = 1 and j = 2 then
                        c := top2[3];
                    elif i = 1 and j = 3 then
                        c := top2[2];
                    elif i = 2 and j = 1 then
                        c := top2[3];
                    elif i = 2 and j = 3 then
                        c := top2[1];
                    elif i = 3 and j = 1 then
                        c := top2[2];
                    else
                        c := top2[1];
                    fi;

                    e := bottom2[1];
                    if _Eq(bottom2[2], 1 + 2 * c - e) then
                        return simplify(Pi * 2^(1 - 2 * c) * GAMMA(e) * GAMMA(1 + 2 * c - e) /
                            (GAMMA((a + e) / 2) * GAMMA((a + 1 + 2 * c - e) / 2) *
                             GAMMA((e - a + 1) / 2) * GAMMA((2 + 2 * c - a - e) / 2)));
                    fi;

                    e := bottom2[2];
                    if _Eq(bottom2[1], 1 + 2 * c - e) then
                        return simplify(Pi * 2^(1 - 2 * c) * GAMMA(e) * GAMMA(1 + 2 * c - e) /
                            (GAMMA((a + e) / 2) * GAMMA((a + 1 + 2 * c - e) / 2) *
                             GAMMA((e - a + 1) / 2) * GAMMA((2 + 2 * c - a - e) / 2)));
                    fi;
                fi;
            od;
        od;
    fi;

    return FAIL;
end proc:

# Parse k=a..b into variable k and bounds a,b.
_ParseRange := proc(rng)
    local lhs, k, bounds;

    if not type(rng, `=`) then
        error "Second argument must be of form k=a..b";
    fi;

    lhs := op(1, rng);
    bounds := op(2, rng);

    if not type(bounds, `..`) then
        error "Second argument must be of form k=a..b";
    fi;

    k := lhs;
    return k, op(1, bounds), op(2, bounds);
end proc:

# Detect zero tail using HG representation.
# If some top parameter is a non-positive value t, then the term vanishes for k > -t.
# We use cutoff = -max(t | t <= 0), i.e. the earliest termination index.
_HasZeroTailBinomialFactor := proc(tk, k::name, b)
    local hgData, top, i, term, maxNonPos, hasNumericTerm, cutoff, rel;

    hgData := _TermToHG(tk, k);
    if hgData = FAIL then
        return false;
    fi;

    top := hgData[2];
    hasNumericTerm := false;

    for i from 1 to nops(top) do
        term := simplify(top[i]);

        if type(term, nonposint) then
            if (not hasNumericTerm) or term > maxNonPos then
                maxNonPos := term;
                hasNumericTerm := true;
            fi;
        elif _IsNegatedExpr(term) then
            cutoff := simplify(-term);
            if _Eq(b, cutoff) then
                return true;
            fi;
        fi;
    od;

    if hasNumericTerm then
        cutoff := -maxNonPos;
        if _Eq(b, cutoff) then
            return true;
        fi;

        rel := is(b >= cutoff);
        if rel = true then
            return true;
        fi;
    fi;

    return false;
end proc:

# Database-based summation entry point requested in task L4.8.
DatabaseSum := proc(tk, rng)
    local k, a, b, kk, shifted, hgData, top, bottom, z, cfac, val, lo, hi;

    k, a, b := _ParseRange(rng);
    kk := '_k';

    if a <> 0 then
        shifted := subs(k = kk + a, tk);
        if b <> infinity then
            b := b - a;
        fi;

        return DatabaseSum(shifted, kk = 0..b);
    fi;

    if b <> infinity then
        lo := DatabaseSum(tk, k = 0..infinity);
        if lo = FAIL then
            return FAIL;
        fi;

        if _HasZeroTailBinomialFactor(tk, k, b) then
            return simplify(lo);
        fi;

        hi := DatabaseSum(tk, k = (b + 1)..infinity);
        if hi = FAIL then
            return FAIL;
        fi;

        return simplify(lo - hi);
    fi;

    # we now have k=0..infinity

    hgData := _TermToHG(tk, k);
    if hgData = FAIL then
        return FAIL;
    fi;

    cfac := hgData[1];
    top := hgData[2];
    bottom := hgData[3];
    z := hgData[4];

    val := ApplyHGIdentity(top, bottom, z);
    if val = FAIL then
        return FAIL;
    fi;

    return simplify(cfac * val);
end proc:
