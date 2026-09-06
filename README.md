The general rigidity and existence theorems are proved in the text. The supplementary programs check the explicit constructions and the finite counts using integer arithmetic and the Python standard library.

The program \texttt{verify.py} verifies the masks, tilings, prime-power signatures, and (T2) conditions of the explicit aperiodic examples at periods $180$ and $900$. It checks the ordinary product identity \eqref{eq:familyproduct} at periods $180$, $900$, $4500$, and $77\,175$, and twenty independently lifted complements at period $900$. For Appendix~\ref{app:900}, it derives the $36$ layer values, computes the four constant terms by both coefficient convolution and multinomial enumeration, and checks the $360$ periodic cores and their two affine orbits.

The program \texttt{verify\_strengthening.py} checks the exact common divisor, the primitive quotient, all complement slices, and independent recombinations of those slices in sixteen constructions realizing the four stabilizer orders for $(p,q,r)=(2,3,5),(2,3,7),(3,5,11),(5,7,17)$. It also checks the mass criterion of Remark~\ref{rem:masscriterion} for a finite range of coprime scales. These checks supplement the proofs and do not assert an enumeration of general three-prime tilings.

Run the programs from the supplementary directory:
\begin{verbatim}
python verify.py --output verification_results.json
python verify_strengthening.py --output strengthening_results.json
\end{verbatim}
