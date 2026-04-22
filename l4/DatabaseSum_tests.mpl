read "/home/kuba/Desktop/gitproj/symbolic/l4/DatabaseSum.mpl":

Check := proc(label, tk, rng, expected)
    local actual;

    actual := simplify(DatabaseSum(tk, rng));

    print(cat("[", label, "] ", Sum(tk, rng), " = ", convert(actual, string)));

    if not evalb(simplify(actual - expected) = 0) then
        error cat(label, " failed: ", convert(actual, string), " <>", convert(expected, string));
    fi;
end proc:

CheckFail := proc(label, tk, rng)
    local actual;

    actual := simplify(DatabaseSum(tk, rng));
    print(cat("[", label, "] ", Sum(tk, rng), " = ", convert(actual, string)));

    if not evalb(actual = FAIL) then
        error cat(label, " expected FAIL, got: ", convert(actual, string));
    fi;
end proc:

# Base HG checks.
Check("0F0", HGTerm([], [], z, k), k=0..infinity, exp(z));
Check("1F0", HGTerm([a], [], z, k), k=0..infinity, (1 - z)^(-a));
Check("0F0 by cancellation", HGTerm([u], [u], z, k), k=0..infinity, exp(z));
Check("1F0 by cancellation", HGTerm([a, u], [u], z, k), k=0..infinity, (1 - z)^(-a));

# Finite-range and tail-elimination checks.
Check("binomial", binomial(n, k), k=0..n, 2^n);
CheckFail("binomial extended range unsupported", binomial(n, k), k=0..n+3);
CheckFail("binomial from 1 unsupported", binomial(n, k), k=1..n);
CheckFail("binomial from 2 unsupported", binomial(n, k), k=2..n);
Check("Vandermonde", binomial(n, k) * binomial(s, t-k), k=0..n, binomial(n + s, t));
CheckFail("Vandermonde extended range unsupported", binomial(n, k) * binomial(s, t-k), k=0..n+5);
Check("binomial product", binomial(n, k) * binomial(2*n, k), k=0..n, binomial(3*n, n));
CheckFail("binomial product extended range unsupported", binomial(n, k) * binomial(2*n, k), k=0..n+4);

# Normal sums from assignment sheets (L4.3, L4.6-style).
Check("L4.3 exp direct", z^k/k!, k=0..infinity, exp(z));
Check("L4.3 geometric direct", z^k, k=0..infinity, 1/(1-z));
Check("L4.3 binomial theorem direct", binomial(a, k) * x^k, k=0..infinity, (1 + x)^a);
Check("alternating binomial", (-1)^k * binomial(n, k), k=0..n, 0);
Check("L4.6 b-type", binomial(n, k) * binomial(s, t + k), k=0..n, binomial(s + n, s - t));
Check("L4.6 d-type", (-1)^k * binomial(n, k) * binomial(2*n - k, m - k), k=0..n,
    binomial(2*n, m) * pochhammer(-n, m) / pochhammer(-2*n, m));

CheckFail("L4.3 ln(1+x) direct unsupported", (-1)^(k + 1) * x^k / k, k=1..infinity);
CheckFail("L4.3 sin direct unsupported", (-1)^k * x^(2*k + 1) / (2*k + 1)!, k=0..infinity);
CheckFail("L4.3 cos direct unsupported", (-1)^k * x^(2*k) / (2*k)!, k=0..infinity);
CheckFail("L4.6 f-type unsupported", binomial(n, k) * (k + 3*a)! / (k + a)!, k=0..n);

# Sums from previous sheets (L2.9 and L1.13-style).
Check("L2.9 a) p=3", (-1)^k * binomial(n, k)^3, k=0..n,
    GAMMA(1 + 3*n/2) / GAMMA(1 + n/2)^3 * cos(Pi*n/2));
CheckFail("L2.9 a) p=2 unsupported", (-1)^k * binomial(n, k)^2, k=0..n);
Check("L2.9 c) central square", binomial(2*n, k)^2, k=0..2*n, binomial(4*n, 2*n));
Check("L2.9 c) Vandermonde form", binomial(2*n, k) * binomial(2*n, 2*n-k), k=0..2*n, binomial(4*n, 2*n));
CheckFail("L2.9 c) extended range unsupported", binomial(2*n, k)^2, k=0..2*n+2);
CheckFail("L1.13 alternating zeta-like unsupported", (-1)^k / k^6, k=1..infinity);

# 2F1 identities.
Check("Gauss", HGTerm([a, b], [c], 1, k), k=0..infinity,
    GAMMA(c) * GAMMA(c - a - b) / (GAMMA(c - a) * GAMMA(c - b)));
Check("Gauss swapped", HGTerm([b, a], [c], 1, k), k=0..infinity,
    GAMMA(c) * GAMMA(c - a - b) / (GAMMA(c - a) * GAMMA(c - b)));
Check("Chu-Vandermonde", HGTerm([-n, b], [c], 1, k), k=0..infinity,
    pochhammer(c - b, n) / pochhammer(c, n));
Check("Chu-Vandermonde swapped", HGTerm([b, -n], [c], 1, k), k=0..infinity,
    pochhammer(c - b, n) / pochhammer(c, n));
Check("Chu finite", HGTerm([-n, b], [c], 1, k), k=0..n, pochhammer(c - b, n) / pochhammer(c, n));
CheckFail("Chu extended finite unsupported", HGTerm([-n, b], [c], 1, k), k=0..n+2);
Check("Kummer", HGTerm([a, b], [1 + a - b], -1, k), k=0..infinity,
    2^(-a) * GAMMA(1 + a - b) * sqrt(Pi) / (GAMMA((a + 1)/2) * GAMMA(1 + a/2 - b)));
Check("Kummer swapped", HGTerm([b, a], [1 + b - a], -1, k), k=0..infinity,
    2^(-b) * GAMMA(1 + b - a) * sqrt(Pi) / (GAMMA((b + 1)/2) * GAMMA(1 + b/2 - a)));
Check("half argument", HGTerm([a, 1 - a], [b], 1/2, k), k=0..infinity,
    2^(1 - b) * sqrt(Pi) * GAMMA(b) / (GAMMA((a + b)/2) * GAMMA((b - a + 1)/2)));
Check("half argument swapped", HGTerm([1 - a, a], [b], 1/2, k), k=0..infinity,
    2^(1 - b) * sqrt(Pi) * GAMMA(b) / (GAMMA((a + b)/2) * GAMMA((b - a + 1)/2)));

# 3F2 identities.
Check("Pfaff-Saalschutz", HGTerm([-n, a, b], [c, 1 + a + b - c - n], 1, k), k=0..infinity,
    pochhammer(c - a, n) * pochhammer(c - b, n) / (pochhammer(c, n) * pochhammer(c - a - b, n)));
Check("Pfaff-Saalschutz neg in 2nd", HGTerm([a, -n, b], [c, 1 + a + b - c - n], 1, k), k=0..infinity,
    pochhammer(c - a, n) * pochhammer(c - b, n) / (pochhammer(c, n) * pochhammer(c - a - b, n)));
Check("Pfaff-Saalschutz neg in 3rd", HGTerm([a, b, -n], [c, 1 + a + b - c - n], 1, k), k=0..infinity,
    pochhammer(c - a, n) * pochhammer(c - b, n) / (pochhammer(c, n) * pochhammer(c - a - b, n)));
Check("Dixon", HGTerm([a, b, c], [1 + a - b, 1 + a - c], 1, k), k=0..infinity,
    GAMMA(1 + a/2) * GAMMA(1 + a - b) * GAMMA(1 + a - c) * GAMMA(1 + a/2 - b - c) /
    (GAMMA(1 + a) * GAMMA(1 + a/2 - b) * GAMMA(1 + a/2 - c) * GAMMA(1 + a - b - c)));
Check("Dixon with b as pivot", HGTerm([b, a, c], [1 + b - a, 1 + b - c], 1, k), k=0..infinity,
    GAMMA(1 + b/2) * GAMMA(1 + b - a) * GAMMA(1 + b - c) * GAMMA(1 + b/2 - a - c) /
    (GAMMA(1 + b) * GAMMA(1 + b/2 - a) * GAMMA(1 + b/2 - c) * GAMMA(1 + b - a - c)));
Check("Watson", HGTerm([a, b, c], [(a + b + 1)/2, 2*c], 1, k), k=0..infinity,
    sqrt(Pi) * GAMMA(c + 1/2) * GAMMA((a + b + 1)/2) * GAMMA(c + (1 - a - b)/2) /
    (GAMMA((a + 1)/2) * GAMMA((b + 1)/2) * GAMMA(c + (1 - a)/2) * GAMMA(c + (1 - b)/2)));
Check("Watson reordered top", HGTerm([c, b, a], [(a + b + 1)/2, 2*c], 1, k), k=0..infinity,
    sqrt(Pi) * GAMMA(c + 1/2) * GAMMA((a + b + 1)/2) * GAMMA(c + (1 - a - b)/2) /
    (GAMMA((a + 1)/2) * GAMMA((b + 1)/2) * GAMMA(c + (1 - a)/2) * GAMMA(c + (1 - b)/2)));
Check("Whipple", HGTerm([a, 1 - a, c], [e, 1 + 2*c - e], 1, k), k=0..infinity,
    Pi * 2^(1 - 2*c) * GAMMA(e) * GAMMA(1 + 2*c - e) /
    (GAMMA((a + e)/2) * GAMMA((a + 1 + 2*c - e)/2) * GAMMA((e - a + 1)/2) * GAMMA((2 + 2*c - a - e)/2)));
Check("Whipple swapped bottom", HGTerm([a, 1 - a, c], [1 + 2*c - e, e], 1, k), k=0..infinity,
    Pi * 2^(1 - 2*c) * GAMMA(e) * GAMMA(1 + 2*c - e) /
    (GAMMA((a + e)/2) * GAMMA((a + 1 + 2*c - e)/2) * GAMMA((e - a + 1)/2) * GAMMA((2 + 2*c - a - e)/2)));
