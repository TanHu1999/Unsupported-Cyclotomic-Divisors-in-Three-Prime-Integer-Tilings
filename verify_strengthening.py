#!/usr/bin/env python3
"""Exact checks of the new quotient, stabilizer, and mass statements.

These finite checks supplement the proofs; they do not certify general theorems.
Run: python verify_strengthening.py --output strengthening_results.json
"""
from argparse import ArgumentParser
from itertools import combinations, product
from math import gcd
from pathlib import Path
import json
from verify import require, stabilizer, verify_tiling, verify_signature_and_t2, vanishes_at_order


def mass_checks():
    cases = solutions = 0
    for p,q in combinations((2,3,5,7,11,13),2):
        for L in range(1,p*q+2):
            if gcd(L,p*q)>1:
                continue
            member = any((L-p*a)>=0 and (L-p*a)%q==0 for a in range(L//p+1))
            extra = False
            for W in range(p*q//L+1):
                for U in range(q+1):
                    remainder=p*q-L*W-p*U
                    if remainder>=0 and remainder%q==0:
                        solutions+=1
                        extra |= W>0
            require(member == (not extra), f"Mass criterion failed at {(p,q,L)}")
            cases+=1
    return {'coprime_scale_cases':cases,'nonnegative_solutions_checked':solutions}


def realization(p,q,r,change_f,change_g):
    a,b=next((a,b) for a in range(1,r//p+1) for b in range(1,r//q+1) if p*a+q*b==r)
    layers=[([i]*q,[0]*p) for _ in range(a) for i in range(p)]
    layers += [([0]*q,[j]*p) for _ in range(b) for j in range(q)]
    if change_f:
        layers[0]=([0]*(q-1)+[1],[0]*p)
        layers[1]=([1]*(q-1)+[0],[0]*p)
    if change_g:
        k=a*p
        layers[k]=([0]*q,[0]*(p-1)+[1])
        layers[k+1]=([0]*q,[1]*(p-1)+[0])
    M=(p*q*r)**2
    mods=(p*p,q*q,r*r)
    crt_weights=[(M//s)*pow(M//s,-1,s) for s in mods]
    def crt(x,y,z):
        return (crt_weights[0]*x+crt_weights[1]*y+crt_weights[2]*z)%M
    A=sorted(crt(p*u+f[v],q*v+g[u],r*w) for w,(f,g) in enumerate(layers) for u in range(p) for v in range(q))
    B=sorted(crt(x,y,z) for x,y,z in product(range(p),range(q),range(r)))
    verify_tiling(A,B,M)
    expected=(1 if change_g else p)*(1 if change_f else q)
    require(len(stabilizer(A,M))==expected,'Wrong stabilizer order')
    require(stabilizer(B,M)==[0],'Standard complement not aperiodic')
    verify_signature_and_t2(A,M,[p*p,q*q,r*r])
    require(vanishes_at_order(A,p*q*r),'Missing full low-order zero')
    g=gcd(M,*(x-A[0] for x in A))
    require(g==r,'Incorrect exact common divisor')
    C=[x//r for x in A]
    require(all(x%r==0 for x in A),'Confinement failed')
    require(gcd(M//r,*(x-C[0] for x in C))==1,'Quotient not primitive')
    verify_signature_and_t2(C,M//r,[p*p,q*q,r])
    require(vanishes_at_order(C,p*q),'Quotient low zero failed')
    slices=[]
    for j in range(r):
        D=[(x-j)//r for x in B if x%r==j]
        verify_tiling(C,D,M//r)
        slices.append(D)
    # Translate each quotient complement independently, then reconstruct B.
    lifted=sorted(j+r*((d+j*j+1)%(M//r)) for j,D in enumerate(slices) for d in D)
    verify_tiling(A,lifted,M)
    return {'primes':[p,q,r],'modulus':M,'modified_f':change_f,'modified_g':change_g,
            'stabilizer_order':expected,'gcd_M_A_minus_A':g,
            'primitive_quotient':True,'complement_slices_checked':r,
            'independent_slice_recombination':True}


def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    results={'status':'passed','arithmetic':'exact integers; Python standard library',
             'scope':'Finite examples of the added statements; the manuscript supplies general proofs',
             'mass_criterion':mass_checks(),
             'stabilizer_and_quotient_cases':[realization(p,q,r,f,g) for p,q,r in [(2,3,5),(2,3,7),(3,5,11),(5,7,17)] for f,g in product((False,True),repeat=2)]}
    output=json.dumps(results,indent=2,sort_keys=True)+'\n'
    if args.output:
        args.output.write_text(output,encoding='utf-8')
    print(output,end='')

if __name__=='__main__':
    main()
