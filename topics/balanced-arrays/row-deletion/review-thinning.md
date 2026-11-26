# Independent review of the row-thinning obstruction

I verified the obstruction for every fixed shape $1\le r\le d$ with $r\nmid d$, the three-column schedule, and the exact finite example. The result concerns the expected polynomial under independent row retention. The original deterministic conjecture remains separate.

## Capacity and the optional-row bound

Put $m=\lfloor Nr/d\rfloor$, $s=Nr-dm$, and $u_j=\lceil(dj-s)/r\rceil$ for $j\ge1$. The capacity inequality is necessary, and cyclically assigning $d(m+j)$ cells to successive groups of size at most $r$ attains it. Since $dj-s>0$, the leading term in the mixed coefficient for quota $m+j$ has exponent $u_j$ and coefficient $\binom M{u_j}a_{N+u_j,m+j}>0$ when $M\ge u_j$. The quota $m$ has exponent zero.

With $g=\gcd(d,r)$ and $P=r/g$, the differences $\delta_j=u_j-u_{j-1}$ for $j\ge2$ satisfy $\delta_{j+P}=\delta_j$. Their period average is $(d/g)/P=d/r$. Since $r\nmid d$, both the floor and ceiling values occur, and there is a drop $\delta_j>\delta_{j+1}$ with $2\le j\le P+1$, allowing the drop across the end of the period. At this quota the exponent of the coefficient ratio is $2u_j-u_{j-1}-u_{j+1}=\delta_j-\delta_{j+1}>0$. Taking $M=u_{j+1}\le\lceil d(P+2)/r\rceil$ includes both neighbors. The same shape-dependent upper bound can also be used as a common choice of $M$ for every $N$, since additional optional rows preserve the leading powers and positive leading coefficients. This establishes failure for all sufficiently small positive $p$ at each fixed $N$. I separately tested the drop and the bound over 311,471 shape and base-residue combinations with $d\le100$.

## Schedule at three columns

When $d=3,r=2$ and $N=3u$, the first three exponents are $0,2,3$ and $M=3$ suffices. At the extremes, the full rows omit each column equally often, giving $A=N!/(u!)^3$ and $D=(N+3)!/((u+1)!)^3$. At $N+2$ and quota $2u+1$, there is one singleton row. For a fixed singleton column, the $N+1$ full rows omit that column $u+1$ times and the other two columns $u$ times each. Choosing the singleton row and its column gives $B=3(N+2)!/[(u+1)!(u!)^2]$. The slack for $C$ is three, so the deficient rows consist of either three singletons or one singleton and one empty row. There are $O(N^3)$ ways to fix them. For each choice, assignments to full rows can be injected into words of length $N+3$ with a prescribed histogram by padding with a fixed column. The largest histogram count at that length is $D$. Thus $B/A=O(N)$, $C/A=O(N^3)$, and $D/A\to27$.

For any sequence $p_N\in(0,1)$ on positive multiples of three satisfying $N^2p_N\to0$, the displayed upper bound for the coefficient ratio is $O(p_NN^2)=o(1)$. In particular, $p_N C/A=o(N)$ in its numerator and $(1-p_N)^3\to1$ in its denominator. The failure is eventual along every such sequence.

## Exact certificate and scope

I independently convolved the seven allowed row monomials, starting with coefficient one at $(0,0,0)$ and adding the indicator vector of each possible row. The resulting diagonal coefficient lists, in ascending order, are $(1,24,6)$, $(1,60,114)$, $(1,120,690,180)$, and $(1,210,2640,2940,90)$ at $n=3,4,5,6$. Substituting these counts and $p=1/500$ gives mixed coefficients
$(b_2,b_3,b_4)=(415851453/62500000,\ 681/312500,\ 9/12500000)$. The signed excess $b_2b_4-b_3^2$ is the positive rational $32575077/781250000000000$. The log-concavity margin $b_3^2-b_2b_4$ is its negative. Each of the four deterministic coefficient lists satisfies the strict ratio test with factor four, so all four have simple negative roots.

The only wording correction I recommend is to call the displayed quantity in the schedule the ordinary coefficient ratio. Calling it normalized curvature can suggest division of the coefficients by binomial factors. Define the direction of subtraction whenever the script or note says “Newton gap.” The claim that all four deterministic members are real-rooted for every base $N$ also merits a precise citation to the corank-one theorem. The asymptotic obstruction only needs the available eventual result to place all four deterministic members in a real-rooted range arbitrarily late. Averaging them establishes no failure of an individual deterministic polynomial or of the single-row deletion implication.

**Signed** — Independent mathematical reviewer, agent-assisted.
