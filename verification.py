#!/usr/bin/env python3
"""Exact finite checks for Unsupported Cyclotomic Divisors in Three-Prime Tilings.

Run with Python 3.9 or later: python3 verification.py
Only the Python standard library is used.  No floating-point arithmetic, network
access, external data, or manuscript file is needed.  Failed checks raise an
AssertionError; successful checks print a JSON report.  These finite checks
supplement, and do not replace, the general proofs in the manuscript.

The program independently checks:
* Laurent constant terms by convolution and by multinomial enumeration;
* the same counts by enumeration of actual ordered low-digit layers;
* all 360 periodic cores, their affine orbits and cyclotomic zeros;
* every complement of every core by an exact-cover search;
* the displayed periodic/aperiodic examples, CRT coordinates, stabilizers,
  prime-power signatures, (T2), and tiling identities;
* the general layer construction of all four stabilizer orders for several
  prime triples, using exact polynomial division and finite cyclic groups.
"""

from collections import Counter
from functools import lru_cache
from itertools import combinations_with_replacement, product
from math import factorial, gcd
import json


def trim(poly):
    poly = list(poly)
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def divmod_monic(poly, divisor):
    """Integer polynomial division; coefficient lists are in ascending order."""
    poly, divisor = trim(poly), trim(divisor)
    assert divisor[-1] == 1
    quotient = [0] * max(1, len(poly) - len(divisor) + 1)
    while len(poly) >= len(divisor) and poly != [0]:
        shift, coefficient = len(poly) - len(divisor), poly[-1]
        quotient[shift] = coefficient
        for j, entry in enumerate(divisor):
            poly[shift + j] -= coefficient * entry
        poly = trim(poly)
    return trim(quotient), poly


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


@lru_cache(None)
def cyclotomic(n):
    poly = [-1] + [0] * (n - 1) + [1]
    for d in divisors(n):
        if d < n:
            poly, remainder = divmod_monic(poly, cyclotomic(d))
            assert remainder == [0]
    return tuple(poly)


def zeros_among_divisors(points, modulus):
    points = set(points)
    assert points and all(0 <= x < modulus for x in points)
    poly = [int(j in points) for j in range(max(points) + 1)]
    return sorted(d for d in divisors(modulus) if d > 1
                  and divmod_monic(poly, cyclotomic(d))[1] == [0])


def prime_power_base(n):
    for p in range(2, n + 1):
        if n % p == 0:
            while n % p == 0:
                n //= p
            return p if n == 1 else None
    return None


def signature(zeros):
    return [d for d in zeros if prime_power_base(d) is not None]


def check_t2(zeros):
    sig, zeros = signature(zeros), set(zeros)
    for mask in range(1, 1 << len(sig)):
        chosen = [sig[j] for j in range(len(sig)) if mask & (1 << j)]
        bases = [prime_power_base(d) for d in chosen]
        if len(set(bases)) == len(bases):
            order = 1
            for d in chosen:
                order *= d
            assert order in zeros, (sig, order)


def check_tiling(a, b, modulus):
    a, b = set(a), set(b)
    assert len(a) * len(b) == modulus
    counts = Counter((x + y) % modulus for x in a for y in b)
    assert len(counts) == modulus and set(counts.values()) == {1}


def stabilizer(points, modulus):
    points = set(points)
    base = min(points)
    candidates = {(x - base) % modulus for x in points}
    return sorted(t for t in candidates
                  if {(x + t) % modulus for x in points} == points)


def difference_gcd(points, modulus):
    base, result = min(points), modulus
    for x in points:
        result = gcd(result, x - base)
    return result


def crt(values, moduli):
    modulus = 1
    for m in moduli:
        modulus *= m
    return sum(x * (modulus // m) * pow(modulus // m, -1, m)
               for x, m in zip(values, moduli)) % modulus


def k_polynomial(scales):
    coefficients = Counter()
    for s, weight in scales:
        for point in ((s, 0), (-s, 0), (0, s), (0, -s), (s, s), (-s, -s)):
            coefficients[point] += weight
    return coefficients


def constant_term_convolution(coefficients, power=5):
    previous = {(0, 0): 1}
    for _ in range(power):
        current = Counter()
        for (x, y), value in previous.items():
            for (a, b), coefficient in coefficients.items():
                current[x + a, y + b] += value * coefficient
        previous = current
    return previous.get((0, 0), 0)


def constant_term_multinomial(coefficients, power=5):
    """Independent expansion over unordered monomial multisets."""
    terms = sorted(coefficients)
    total = 0
    for indices in combinations_with_replacement(range(len(terms)), power):
        if (sum(terms[j][0] for j in indices),
                sum(terms[j][1] for j in indices)) != (0, 0):
            continue
        denominator, weight = 1, 1
        for index, count in Counter(indices).items():
            denominator *= factorial(count)
            weight *= coefficients[terms[index]] ** count
        total += (factorial(power) // denominator) * weight
    return total


ROOTS_3 = ((1, 0), (0, 1), (-1, -1))


def layer_types():
    layers = []
    for f in product(range(2), repeat=3):
        for g in product(range(3), repeat=2):
            f_constant, g_constant = len(set(f)) == 1, len(set(g)) == 1
            if f_constant or g_constant:
                fsum = sum((-1) ** value for value in f)
                character = tuple(fsum * sum(ROOTS_3[value][j] for value in g)
                                  for j in range(2))
                layers.append((f, g, character, f_constant, g_constant))
    assert len(layers) == 36
    assert Counter(layer[2] for layer in layers) == k_polynomial(((6, 1), (3, 2), (2, 3)))
    return layers


def ordered_layer_counts(layers):
    """Enumerate four actual layers, then exactly match each possible fifth.

    High digits label layers, so choices counted here are distinct subsets for
    one fixed low-5 residue.  Constant-vector flags determine the order-2 and
    order-3 periods; no order-5 period is possible for a zero sum.
    """
    by_character = {}
    for i, layer in enumerate(layers):
        by_character.setdefault(layer[2], []).append(i)
    counts = Counter()
    for indices in product(range(len(layers)), repeat=4):
        partial = [layers[i] for i in indices]
        target = (-sum(item[2][0] for item in partial),
                  -sum(item[2][1] for item in partial))
        for last in by_character.get(target, ()):
            chosen = partial + [layers[last]]
            period2 = all(item[4] for item in chosen)
            period3 = all(item[3] for item in chosen)
            order = (2 if period2 else 1) * (3 if period3 else 1)
            counts[order] += 1
    return dict(sorted(counts.items()))


ROOTS_6 = ((1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1))


def enumerate_cores():
    cores = set()
    for lifts in product(range(6), repeat=5):
        core = tuple(sorted(t + 5 * lifts[t] for t in range(5)))
        if all(sum(ROOTS_6[x % 6][j] for x in core) == 0 for j in range(2)):
            cores.add(core)
    assert len(cores) == 360
    return cores


def affine_orbit(core, modulus=30):
    return {tuple(sorted((unit * x + offset) % modulus for x in core))
            for unit in range(modulus) if gcd(unit, modulus) == 1
            for offset in range(modulus)}


def all_core_complements(core, modulus=30):
    """Exact-cover search over all translates, independent of Fourier claims."""
    rows = [sum(1 << ((x + shift) % modulus) for x in core)
            for shift in range(modulus)]
    full = (1 << modulus) - 1
    solutions = set()

    def visit(covered, chosen):
        if covered == full:
            solutions.add(tuple(sorted(chosen)))
            return
        missing = full ^ covered
        first_bit = missing & -missing
        for shift, row in enumerate(rows):
            if row & first_bit and not row & covered:
                visit(covered | row, chosen + (shift,))

    visit(0, ())
    return solutions


def set_from_layers(p, q, r, layers, low_r=0):
    assert len(layers) == r
    return {crt((p * u + f[v], q * v + g[u], r * w + low_r),
                (p * p, q * q, r * r))
            for w, (f, g) in enumerate(layers)
            for u in range(p) for v in range(q)}


def standard_complement(p, q, r):
    return {crt(point, (p * p, q * q, r * r))
            for point in product(range(p), range(q), range(r))}


def verify_example(a, b, modulus, expected_signature, expected_stabilizer,
                   unsupported_order):
    check_tiling(a, b, modulus)
    za, zb = zeros_among_divisors(a, modulus), zeros_among_divisors(b, modulus)
    assert signature(za) == expected_signature
    assert len(stabilizer(a, modulus)) == expected_stabilizer
    assert unsupported_order in za
    for base in set(prime_power_base(d) for d in divisors(unsupported_order) if d > 1):
        if base is None:
            continue
        power = base
        while unsupported_order % (power * base) == 0:
            power *= base
        assert power not in za and len(a) % base == 0
    check_t2(za)
    check_t2(zb)
    return {"A_size": len(a), "B_size": len(b), "A_signature": signature(za),
            "B_signature": signature(zb), "A_stabilizer_order": len(stabilizer(a, modulus)),
            "B_stabilizer_order": len(stabilizer(b, modulus)),
            "A_difference_gcd": difference_gcd(a, modulus),
            "A_zeros_among_period_divisors": za}


def verify_displayed_examples():
    core = (0, 2, 3, 4, 6)
    periodic180 = {30 * j + c for j in range(6) for c in core}
    periodic900 = {150 * j + 5 * c for j in range(6) for c in core}
    b900 = {t + 25 * j for t in range(5) for j in range(6)}
    layers = [((0, 0, 1), (0, 0)), ((0, 1, 1), (0, 0)),
              ((0, 0, 0), (0, 1)), ((0, 0, 0), (0, 1)),
              ((0, 0, 0), (2, 2))]
    a = set_from_layers(2, 3, 5, layers)
    b = standard_complement(2, 3, 5)
    assert sorted(a) == [0,10,20,60,105,170,180,190,240,255,300,310,320,360,375,
                         450,470,490,540,555,610,620,630,660,705,750,770,790,825,840]
    assert sorted(b) == [0,1,28,29,100,101,128,153,200,225,252,253,325,352,353,
                         425,452,477,504,576,577,604,676,677,704,729,776,801,828,829]
    c, d = {x // 5 for x in a}, {x // 5 for x in b if x % 5 == 0}
    assert sorted(c) == [0,2,4,12,21,34,36,38,48,51,60,62,64,72,75,
                         90,94,98,108,111,122,124,126,132,141,150,154,158,165,168]
    assert sorted(d) == [0,20,40,45,65,85]
    assert {(x % 4, x % 9, x % 5) for x in d} == set(product((0, 1), (0, 2, 4), (0,)))
    report = {
        "periodic_180": verify_example(periodic180, {5*j for j in range(6)},
                                      180, [4, 5, 9], 6, 6),
        "periodic_900": verify_example(periodic900, b900, 900, [4, 9, 25], 6, 30),
        "aperiodic_900": verify_example(a, b, 900, [4, 9, 25], 1, 30),
        "aperiodic_180": verify_example(c, d, 180, [4, 5, 9], 1, 6),
    }
    assert report["aperiodic_900"]["B_stabilizer_order"] == 1
    assert report["aperiodic_180"]["B_stabilizer_order"] == 1
    assert difference_gcd(a, 900) == 5 and difference_gcd(c, 180) == 1
    # Check an independently lifted member of the complete complement family.
    lifted = {t + 5*((2*t+1) % 5) + 25*j + 150*((t+2*j+1) % 6)
              for t in range(5) for j in range(6)}
    check_tiling(periodic900, lifted, 900)
    assert signature(zeros_among_divisors(lifted, 900)) == [2, 3, 5]
    return report


def verify_general_stabilizer_construction():
    report = {}
    for p, q, r in ((2, 3, 5), (3, 5, 11), (5, 7, 17)):
        a, b = next((a, b) for a in range(1, r) for b in range(1, r)
                    if a*p + b*q == r)
        initial = []
        for _ in range(a):
            initial.extend([((i,)*q, (0,)*p) for i in range(p)])
        q_start = len(initial)
        for _ in range(b):
            initial.extend([((0,)*q, (j,)*p) for j in range(q)])
        complement = standard_complement(p, q, r)
        modulus = (p*q*r)**2
        assert len(stabilizer(complement, modulus)) == 1
        orders = []
        for change_f, change_g in product((False, True), repeat=2):
            layers = list(initial)
            if change_f:
                layers[0] = ((0,)*(q-1)+(1,), (0,)*p)
                layers[1] = ((1,)*(q-1)+(0,), (0,)*p)
            if change_g:
                layers[q_start] = ((0,)*q, (0,)*(p-1)+(1,))
                layers[q_start+1] = ((0,)*q, (1,)*(p-1)+(0,))
            points = set_from_layers(p, q, r, layers)
            expected = (1 if change_g else p) * (1 if change_f else q)
            assert len(stabilizer(points, modulus)) == expected
            assert difference_gcd(points, modulus) == r
            check_tiling(points, complement, modulus)
            # The order-pqr zero uses a polynomial of degree below pqr, so this
            # check does not construct polynomials of degree equal to the period.
            low_counts = Counter(x % (p*q*r) for x in points)
            low_mask = [low_counts[j] for j in range(p*q*r)]
            assert divmod_monic(low_mask, cyclotomic(p*q*r))[1] == [0]
            orders.append(expected)
        report[f"{p},{q},{r}"] = sorted(orders)
    return report


def main():
    specifications = {
        "all": (((6, 1), (3, 2), (2, 3)), 366960),
        "order_2_period": (((6, 1), (2, 3)), 146160),
        "order_3_period": (((6, 1), (3, 2)), 46200),
        "order_6_period": (((6, 1),), 360),
    }
    constant_terms = {}
    for label, (scales, expected) in specifications.items():
        polynomial = k_polynomial(scales)
        convolution = constant_term_convolution(polynomial)
        multinomial = constant_term_multinomial(polynomial)
        assert convolution == multinomial == expected
        constant_terms[label] = {"convolution": convolution, "multinomial": multinomial}
    counts = ordered_layer_counts(layer_types())
    assert counts == {1: 174960, 2: 145800, 3: 45840, 6: 360}
    assert sum(counts.values()) == constant_terms["all"]["convolution"]
    cores = enumerate_cores()
    representatives = ((0, 2, 3, 4, 6), (0, 1, 3, 9, 17))
    orbits = [affine_orbit(core) for core in representatives]
    assert [len(orbit) for orbit in orbits] == [120, 240]
    assert not orbits[0] & orbits[1] and orbits[0] | orbits[1] == cores
    expected_complements = {tuple(range(a, 30, 5)) for a in range(5)}
    for core in sorted(cores):
        assert zeros_among_divisors(core, 30) == [5, 6]
        assert all_core_complements(core) == expected_complements
    report = {
        "status": "all exact finite checks passed",
        "constant_terms": constant_terms,
        "ordered_actual_layers_fixed_low_5": counts,
        "all_five_low_5_residues": {order: 5*count for order, count in counts.items()},
        "total_subsets_900": 5*sum(counts.values()),
        "periodic_cores": len(cores),
        "core_affine_orbits": [{"representative": list(core), "size": len(orbit)}
                              for core, orbit in zip(representatives, orbits)],
        "core_divisor_zeros_all_360": [5, 6],
        "complements_each_core_exact_cover": [list(c) for c in sorted(expected_complements)],
        "complements_each_periodic_900_set": 5**5 * 6**30,
        "explicit_examples": verify_displayed_examples(),
        "stabilizer_construction": verify_general_stabilizer_construction(),
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
