#!/usr/bin/env python3
"""Exact, standard-library checks accompanying unsupported.tex.

This program verifies displayed examples and finite enumeration constants.
It does not replace the manuscript's general arguments or claim to exhaust
all three-prime parameter choices. No floating-point arithmetic is used.

Run: python verify.py --output verification_results.json
"""
from argparse import ArgumentParser
from collections import Counter
from functools import lru_cache
from itertools import combinations_with_replacement, product
from math import factorial, gcd
from pathlib import Path
from random import Random
import json


def require(condition, message):
    if not condition:
        raise AssertionError(message)


@lru_cache(None)
def factorization(n):
    factors = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            e = 0
            while n % p == 0:
                e += 1
                n //= p
            factors.append((p, e))
        p += 1
    if n > 1:
        factors.append((n, 1))
    return tuple(factors)


@lru_cache(None)
def divisors(n):
    ds = [1]
    for p, e in factorization(n):
        ds = [d * p**j for d in ds for j in range(e + 1)]
    return tuple(sorted(ds))


def trim(a):
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def polynomial_quotient(a, b):
    """Exact division by a monic integer polynomial, low degrees first."""
    a = list(a)
    require(b[-1] == 1 and len(a) >= len(b), "Invalid exact division")
    result = [0] * (len(a) - len(b) + 1)
    terms = [(i, c) for i, c in enumerate(b) if c]
    for i in range(len(result) - 1, -1, -1):
        c = a[i + len(b) - 1]
        result[i] = c
        if c:
            for j, v in terms:
                a[i + j] -= c * v
    require(not any(a), "Polynomial division has nonzero remainder")
    return tuple(trim(result))


@lru_cache(None)
def squarefree_cyclotomic(n):
    """Only called at squarefree orders, small in the checks below."""
    require(all(e == 1 for _, e in factorization(n)), "Non-squarefree order")
    a = (-1,) + (0,) * (n - 1) + (1,)
    for d in divisors(n):
        if d < n:
            a = polynomial_quotient(a, squarefree_cyclotomic(d))
    return a


def vanishes_at_order(points, d):
    """Test exact divisibility by Phi_d for a mask, using integer arithmetic.

    For R=rad(d), k=d/R, Phi_d(X)=Phi_R(X^k). Divide each
    residue class of exponents modulo k separately by Phi_R.
    """
    radical = 1
    for p, _ in factorization(d):
        radical *= p
    k = d // radical
    poly = squarefree_cyclotomic(radical)
    terms = [(i, c) for i, c in enumerate(poly) if c]
    bins = {}
    for x in points:
        x %= d
        residue = x % k
        if residue not in bins:
            bins[residue] = [0] * radical
        bins[residue][x // k] += 1
    degree = len(poly) - 1
    for coefficients in bins.values():
        for j in range(radical - 1, degree - 1, -1):
            c = coefficients[j]
            if c:
                for i, v in terms:
                    coefficients[j - degree + i] -= c * v
        if any(coefficients):
            return False
    return True


def divisor_zeros(points, modulus):
    return [d for d in divisors(modulus) if d > 1 and vanishes_at_order(points, d)]


def stabilizer(points, modulus):
    point_set = set(points)
    first = min(point_set)
    return sorted(t for t in ((x - first) % modulus for x in point_set)
                  if {(x + t) % modulus for x in point_set} == point_set)


def verify_tiling(a, b, modulus):
    require(len(a) == len(set(a)), "Repeated points in A")
    require(len(b) == len(set(b)), "Repeated points in B")
    require(all(0 <= x < modulus for x in a + b), "Nonstandard representatives")
    require(len(a) * len(b) == modulus, "Cardinality product is incorrect")
    convolution = Counter((x + y) % modulus for x in a for y in b)
    require(len(convolution) == modulus and set(convolution.values()) == {1},
            "Cyclic tiling is not direct and complete")


def verify_signature_and_t2(points, modulus, expected_signature):
    signature = sorted(p**j for p, e in factorization(modulus)
                       for j in range(1, e + 1)
                       if vanishes_at_order(points, p**j))
    require(signature == sorted(expected_signature), "Incorrect prime-power signature")
    # The tiling allocation lemma excludes prime-power zeros outside the period.
    groups = []
    cardinality_from_t1 = 1
    for p, _ in factorization(modulus):
        powers = [s for s in signature if factorization(s)[0][0] == p]
        groups.append([1] + powers)
        cardinality_from_t1 *= p**len(powers)
    require(cardinality_from_t1 == len(points), "T1 cardinality fails")
    orders = set()
    for choice in product(*groups):
        d = 1
        for s in choice:
            d *= s
        if d > 1:
            orders.add(d)
    require(all(vanishes_at_order(points, d) for d in orders), "T2 fails")
    return {"signature": signature, "T2_orders": sorted(orders)}


def core_mask(p, q, length):
    def in_semigroup(n):
        return n >= 0 and any(n >= b*q and (n-b*q) % p == 0 for b in range(p))
    degree = length - 1 + (p-1)*(q-1)
    coefficients = [int(in_semigroup(n)) - int(in_semigroup(n-length))
                    for n in range(degree+1)]
    require(all(c in (0, 1) for c in coefficients), "Core is not a 0-1 mask")
    phi = squarefree_cyclotomic(p*q)
    expected = [0] * (length+len(phi)-1)
    for j in range(length):
        for i, c in enumerate(phi):
            expected[i+j] += c
    require(coefficients == expected, "Apery polynomial identity fails")
    support = [i for i, c in enumerate(coefficients) if c]
    require(len(support) == length and len({x % length for x in support}) == length,
            "Core fails the complete-residue property")
    return support


def verify_ordinary_product(a, b, modulus, q, h):
    """Check A(X)B(X)=[M]_X Phi_Q(X^h) before reducing modulo X^M-1."""
    left = Counter(x+y for x in a for y in b)
    phi = squarefree_cyclotomic(q)
    degree = modulus - 1 + h*(len(phi)-1)
    differences = [0] * (degree+2)
    for i, c in enumerate(phi):
        differences[h*i] += c
        differences[h*i+modulus] -= c
    current = 0
    for i in range(degree+1):
        current += differences[i]
        require(left.get(i, 0) == current, "Ordinary product identity fails")
    require(not left or max(left) <= degree, "Product degree is too large")


def construction(p, q, r, m, e):
    Q, L, h = p*q, r**m, r**e
    K, M = Q*h*L, Q*Q*h*L
    core = core_mask(p, q, L)
    a = sorted(K*j+h*c for j in range(Q) for c in core)
    b = sorted(t+h*L*j for t in range(h) for j in range(Q))
    verify_tiling(a, b, M)
    verify_ordinary_product(a, b, M, Q, h)
    sa = [p*p, q*q] + [r**j for j in range(e+1, e+m+1)]
    sb = [p, q] + [r**j for j in range(1, e+1)]
    checks = {
        "parameters": {"p": p, "q": q, "r": r, "m": m, "e": e},
        "modulus": M, "cardinalities": [len(a), len(b)],
        "A": verify_signature_and_t2(a, M, sa),
        "B": verify_signature_and_t2(b, M, sb),
        "ordinary_product_identity": True,
    }
    unsupported = [Q*r**j for j in range(e+1)]
    require(all(vanishes_at_order(a, d) for d in unsupported), "Unsupported zero missing")
    for d in unsupported:
        require(all(not vanishes_at_order(a, s**alpha)
                    for s, alpha in factorization(d)), "Claimed zero has support")
    checks["unsupported_orders_checked"] = unsupported
    return a, b, M, checks


def verify_examples():
    def crt(x, y, z):
        return (225*x+100*y+576*z) % 900
    layers = [((0,0,1),(0,0)), ((0,1,1),(0,0)),
              ((0,0,0),(0,1)), ((0,0,0),(0,1)), ((0,0,0),(2,2))]
    a = sorted(crt(2*u+f[v],3*v+g[u],5*w)
               for w,(f,g) in enumerate(layers) for u in range(2) for v in range(3))
    require(a == [0,10,20,60,105,170,180,190,240,255,300,310,320,360,375,
                  450,470,490,540,555,610,620,630,660,705,750,770,790,825,840],
            "Printed 900-point list differs from its layer formula")
    b = sorted(crt(x,y,z) for x in range(2) for y in range(3) for z in range(5))
    require(b == [0,1,28,29,100,101,128,153,200,225,252,253,325,352,353,
                  425,452,477,504,576,577,604,676,677,704,729,776,801,828,829],
            "Printed standard complement differs from its CRT formula")
    c, d = [x//5 for x in a], [x//5 for x in b if x % 5 == 0]
    require(c == [0,2,4,12,21,34,36,38,48,51,60,62,64,72,75,90,94,98,108,
                  111,122,124,126,132,141,150,154,158,165,168], "Printed C180 differs")
    require(d == [0,20,40,45,65,85], "Printed D180 differs")
    require(sorted((x%4,x%9,x%5) for x in d) == sorted(product([0,1],[0,2,4],[0])),
            "D180 CRT formula differs")
    result = {}
    for label, left, right, M, sa, sb, unsupported in [
        ("aperiodic_900",a,b,900,[4,9,25],[2,3,5],30),
        ("aperiodic_180",c,d,180,[4,5,9],[2,3],6),
    ]:
        verify_tiling(left,right,M)
        item = {"modulus":M,"cardinalities":[len(left),len(right)],
                "A":verify_signature_and_t2(left,M,sa),
                "B":verify_signature_and_t2(right,M,sb)}
        for name, points in [("A",left),("B",right)]:
            item[name]["divisor_order_zeros"] = divisor_zeros(points,M)
            item[name]["stabilizer"] = stabilizer(points,M)
            require(item[name]["stabilizer"] == [0], "Displayed example is periodic")
        require(vanishes_at_order(left,unsupported), "Displayed unsupported zero missing")
        require(all(not vanishes_at_order(left,s**alpha)
                    for s,alpha in factorization(unsupported)), "Displayed zero has support")
        item["unsupported_order_checked"] = unsupported
        difference_gcd = M
        for x in left:
            difference_gcd = gcd(difference_gcd,x-left[0])
        item["gcd_M_A_minus_A"] = difference_gcd
        result[label] = item
    return result


def verify_complements(a, b0, modulus):
    rng = Random(20260906)
    mask_b0 = [int(i in b0) for i in range(max(b0)+1)]
    all_periods = Counter()
    for _ in range(20):
        a_t = [rng.randrange(5) for _ in range(5)]
        b = sorted(t+5*a_t[t]+25*j+150*rng.randrange(6)
                   for t in range(5) for j in range(6))
        verify_tiling(a,b,modulus)
        verify_signature_and_t2(b,modulus,[2,3,5])
        polynomial_quotient([int(i in b) for i in range(max(b)+1)],mask_b0)
        all_periods[len(stabilizer(b,modulus))] += 1
    return {"samples":20,"seed":20260906,"modulus":modulus,
            "tiling_signature_T2_and_B0_divisibility":True,
            "stabilizer_size_distribution":dict(sorted(all_periods.items()))}


def constant_term_recurrence(coefficient):
    current = {(0,0):1}
    for _ in range(5):
        new = Counter()
        for (x,y), n in current.items():
            for (a,b), c in coefficient.items():
                new[(x+a,y+b)] += n*c
        current = new
    return current.get((0,0),0)


def constant_term_multinomial(coefficient):
    powers = list(coefficient)
    total = 0
    for inds in combinations_with_replacement(range(len(powers)),5):
        if any(sum(powers[j][i] for j in inds) for i in range(2)):
            continue
        denominator = 1
        for multiplicity in Counter(inds).values():
            denominator *= factorial(multiplicity)
        count = factorial(5)//denominator
        for j in inds:
            count *= coefficient[powers[j]]
        total += count
    return total


def verify_enumeration():
    roots3 = [(1,0),(0,1),(-1,-1)]
    counters = {name:Counter() for name in ["all","period2","period3","period6"]}
    layer_count = 0
    # Derive coefficients from all actual layers, independently of the stated K_s formula.
    for f in product(range(2),repeat=3):
        for g in product(range(3),repeat=2):
            cf, cg = len(set(f)) == 1, len(set(g)) == 1
            if not (cf or cg):
                continue
            layer_count += 1
            fs = sum((-1)**i for i in f)
            value = tuple(fs*sum(roots3[j][i] for j in g) for i in range(2))
            counters["all"][value] += 1
            if cg:
                counters["period2"][value] += 1
            if cf:
                counters["period3"][value] += 1
            if cf and cg:
                counters["period6"][value] += 1
    require(layer_count == 36, "Incorrect layer count")
    def K(s):
        return Counter({(s,0):1,(-s,0):1,(0,s):1,(0,-s):1,(s,s):1,(-s,-s):1})
    def combine(*terms):
        c = Counter()
        for weight, s in terms:
            for power, value in K(s).items():
                c[power] += weight*value
        return c
    expected_polynomials = {
        "all":combine((1,6),(2,3),(3,2)),
        "period2":combine((1,6),(3,2)),
        "period3":combine((1,6),(2,3)),
        "period6":combine((1,6)),
    }
    require(counters == expected_polynomials, "Layer generating functions differ")
    counts = {name:constant_term_recurrence(c) for name,c in counters.items()}
    second = {name:constant_term_multinomial(c) for name,c in counters.items()}
    require(counts == second, "Independent constant-term methods disagree")
    require(counts == {"all":366960,"period2":146160,"period3":46200,"period6":360},
            "Printed constant term is incorrect")
    per_residue = {"1":counts["all"]-counts["period2"]-counts["period3"]+counts["period6"],
                   "2":counts["period2"]-counts["period6"],
                   "3":counts["period3"]-counts["period6"],"6":counts["period6"]}
    require(per_residue == {"1":174960,"2":145800,"3":45840,"6":360},
            "Printed stabilizer table is incorrect")
    # A second finite enumeration: 6^5 complete residue systems modulo 5 in Z30.
    roots6 = [(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)]
    cores = set()
    for lifts in product(range(6),repeat=5):
        core = tuple(sorted(i+5*lifts[i] for i in range(5)))
        if all(sum(roots6[x%6][j] for x in core) == 0 for j in range(2)):
            cores.add(core)
    require(len(cores) == 360, "Incorrect core enumeration")
    require(all(divisor_zeros(c,30) == [5,6] for c in cores), "Extra or missing core zeros")
    units = [u for u in range(30) if gcd(u,30) == 1]
    def orbit(core):
        return {tuple(sorted((u*x+t)%30 for x in core)) for u in units for t in range(30)}
    orbit1, orbit2 = orbit([0,2,3,4,6]), orbit([0,1,3,9,17])
    require(len(orbit1) == 120 and len(orbit2) == 240, "Incorrect affine orbit sizes")
    require(not orbit1 & orbit2 and orbit1 | orbit2 == cores, "Affine orbits do not partition cores")
    return {"layer_choices":layer_count,"constant_terms":counts,"two_methods_agree":True,
            "stabilizer_counts_per_residue":per_residue,
            "stabilizer_counts_all_residues":{k:5*v for k,v in per_residue.items()},
            "total_subsets":5*counts["all"],"aperiodic_subsets":5*per_residue["1"],
            "cores_enumerated":len(cores),"core_divisor_order_zeros":[5,6],
            "affine_orbit_sizes":[len(orbit1),len(orbit2)]}


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,help="Save the verification summary as JSON")
    args = parser.parse_args()
    results = {"status":"passed","arithmetic":"exact integers; Python standard library",
               "scope":"Explicit examples, selected multiscale cases, sampled lifts, and finite counts; not a proof of general rigidity"}
    results["explicit_examples"] = verify_examples()
    cases = [(2,3,5,1,0),(2,3,5,1,1),(2,3,5,1,2),(3,5,7,2,1)]
    results["multiscale_cases"] = []
    for parameters in cases:
        a,b,M,item = construction(*parameters)
        results["multiscale_cases"].append(item)
        if parameters == (2,3,5,1,1):
            results["sampled_complements"] = verify_complements(a,b,M)
    results["enumeration_900"] = verify_enumeration()
    serialized = json.dumps(results,indent=2,sort_keys=True)+"\n"
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(serialized,encoding="utf-8")
    print(serialized,end="")


if __name__ == "__main__":
    main()
