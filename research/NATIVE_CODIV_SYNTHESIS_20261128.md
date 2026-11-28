# Exact Co/Div determinant synthesis

The original definitions at arbitrary target and original weights give
DUPM = transpose DLPM. The two cross terms may be merged without losing
either orientation. With Co=CLPM+CUPM and Div=DLPM+DUPM, the original
second moment Q=Co-Div. Co+Div is the second moment of the absolute
deviations. Both are PSD for nonnegative weights. Div has zero diagonal
and need not be PSD; a positive definite Q implies Co positive definite.

K = (sqrt Co)^(-1) Div (sqrt Co)^(-1) is the actual symmetric operator.
I-K and I+K are PSD by congruence, and det Q = det Co det(I-K).
The actual eigenvalues satisfy -1 <= lambda <= 1; if Q is positive
definite then lambda < 1. Thus
log det Q = log det Co + sum_i log(1-lambda_i).
The further proved sufficient estimate is log det Q <= log det Co -
trace K. Trace K is signed and need not be nonnegative. For example
the two rows (1,1),(1,-1) give Co=[[2,1],[1,2]], Div=[[0,1],[1,0]],
Q=2I; det Q=4 > det Co=3. Thus synthesis is not an unconditional gain.

All identities use the original population and the original target.
The scaled Schur covariance remains exactly target invariant.
NativeCoDivSynthesis attaches the identity to the actual wheel CoDiv.
The signed arithmetic height inequality remains open. No external RH
input or new assumed signed estimate is used.

The hosted kernel checks must finish before the new declarations are
reported as compiled.
