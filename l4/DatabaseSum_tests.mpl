read "DatabaseSum.mpl":

Check := proc(label, actual, expected)
    print("Testing:", label);
    if not evalb(simplify(actual - expected) = 0) then
        error cat(label, " failed: ", convert(actual, string), " <> ", convert(expected, string));
    fi;
end proc:

Check("0F0", DatabaseSum(HGTerm([], [], z, k), k=0..infinity), exp(z));
Check("1F0", DatabaseSum(HGTerm([a], [], z, k), k=0..infinity), (1 - z)^(-a));

Check("binomial", DatabaseSum(binomial(n, k), k=0..n), 2^n);
Check("Vandermonde", DatabaseSum(binomial(n, k) * binomial(s, t-k), k=0..n), binomial(n + s, t));
Check("binomial product", DatabaseSum(binomial(n, k) * binomial(2*n, k), k=0..n), binomial(3*n, n));

Check("Gauss", DatabaseSum(HGTerm([a, b], [c], 1, k), k=0..infinity),
    GAMMA(c) * GAMMA(c - a - b) / (GAMMA(c - a) * GAMMA(c - b)));
Check("Chu-Vandermonde", DatabaseSum(HGTerm([-n, b], [c], 1, k), k=0..infinity),
    pochhammer(c - b, n) / pochhammer(c, n));
Check("Kummer", DatabaseSum(HGTerm([a, b], [1 + a - b], -1, k), k=0..infinity),
    2^(-a) * GAMMA(1 + a - b) * sqrt(Pi) / (GAMMA((a + 1)/2) * GAMMA(1 + a/2 - b)));
Check("half argument", DatabaseSum(HGTerm([a, 1 - a], [b], 1/2, k), k=0..infinity),
    2^(1 - b) * sqrt(Pi) * GAMMA(b) / (GAMMA((a + b)/2) * GAMMA((b - a + 1)/2)));
Check("Pfaff-Saalschutz", DatabaseSum(HGTerm([-n, a, b], [c, 1 + a + b - c - n], 1, k), k=0..infinity),
    pochhammer(c - a, n) * pochhammer(c - b, n) / (pochhammer(c, n) * pochhammer(c - a - b, n)));
Check("Dixon", DatabaseSum(HGTerm([a, b, c], [1 + a - b, 1 + a - c], 1, k), k=0..infinity),
    GAMMA(1 + a/2) * GAMMA(1 + a - b) * GAMMA(1 + a - c) * GAMMA(1 + a/2 - b - c) /
    (GAMMA(1 + a) * GAMMA(1 + a/2 - b) * GAMMA(1 + a/2 - c) * GAMMA(1 + a - b - c)));
Check("Watson", DatabaseSum(HGTerm([a, b, c], [(a + b + 1)/2, 2*c], 1, k), k=0..infinity),
    sqrt(Pi) * GAMMA(c + 1/2) * GAMMA((a + b + 1)/2) * GAMMA(c + (1 - a - b)/2) /
    (GAMMA((a + 1)/2) * GAMMA((b + 1)/2) * GAMMA(c + (1 - a)/2) * GAMMA(c + (1 - b)/2)));
Check("Whipple", DatabaseSum(HGTerm([a, 1 - a, c], [e, 1 + 2*c - e], 1, k), k=0..infinity),
    Pi * 2^(1 - 2*c) * GAMMA(e) * GAMMA(1 + 2*c - e) /
    (GAMMA((a + e)/2) * GAMMA((a + 1 + 2*c - e)/2) * GAMMA((e - a + 1)/2) * GAMMA((2 + 2*c - a - e)/2)));
