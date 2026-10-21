# OpenAI compensation and NNS covariance: ONE mechanism, side-by-side

Date: 2026-10-21. Follow-on to merged #997. Source-level mathematical documentation, not a second proof and not an improved zero-free bound. Every original ideal phase and physical weight must be retained.

## A. OpenAI marked-minus-rescaled compensation simultaneously in NNS

**OpenAI proof authority:** Detector/Compensation.lean: tupleOperation and tupleOperation_one. Detector/Physical.lean: compensatedTuple_one and compensatedPhysicalProbe. Detector/GaussianCompensation.lean: compensationSubsetCoefficient, compensationSubsetProbe and compensatedPhysicalProbe_eq_subsets. Detector/CompensatedTriple.lean: compensatedPhysicalProbe_eq_row_triples.

For a single selected prime p, the ACTUAL upstream theorem is:

    A = conj(eta(p)) * markedPhysicalProbe(...,D=(p),X,Y,Z*Np)
    B = Np^(-3/2) * physicalProbe(...,X/Np,Y/Np,Z)
    compensatedTuple_one = A - B.

In RH_Lean's invertible real Phi coordinate map Phi(z)=(Re z-Im z, Re z+Im z), define
Co0(x,y)=x_+ y_+ + x_- y_- and Div0(x,y)=x_+ y_- + x_- y_+.
Then, with Phi(A)=(xA,yA), Phi(B)=(xB,yB), the EXACT same upstream cancellation is

    |A-B|²
      = |A|² + |B|²
        - {Co0(xA,xB)+Co0(yA,yB)
           -Div0(xA,xB)-Div0(yA,yB)}.

The bracket is xA*xB+yA*yB = 2 Re(A conjugate(B)).
The signed NNS partial moment is therefore the EXACT negative payment already produced by the OpenAI marked-minus-rescaled source, without estimating it or assuming equal even/odd densities.

For K selected slots, GaussianCompensation.lean proves the complete source subset identity:

    compensatedPhysicalProbe
      = sum_{J subset Fin K} sum_{selected prime tuples p}
          [product_i slotWindow_i(Np_i/slotScale_i)] *
          compensationSubsetProbe(eta,C,W0,W1,p,J,X,Y,Z),

    compensationSubsetCoefficient(J)
      = (-1)^|J| * N(p_J)^(-3/2) *
        conjugate(eta(p_complement(J))),

    compensationSubsetProbe(J)
      = compensationSubsetCoefficient(J) *
        markedPhysicalProbe(...,D=(p_complement(J)),
          X/N(p_J),Y/N(p_J),Z*N(p_complement(J))).

One must preserve BOTH the alternating sign and the conjugated ideal character phase, norm power, rescaled X,Y,Z, and physical window. Each complete original summand is one Hecke ideal-labelled complex source atom. Apply RH_Lean's NNS Co-minus-Div Gram to that FULL family BEFORE any triangle inequality. The signed cross-subset pair contributions are then visible exactly.

## B. OpenAI actual marked moment simultaneously in the SAME NNS coordinate

**OpenAI proof authority:**

1. Hecke/DetectorRawFiber.lean, Fiber.physicalProduct: actual physical W(u) is the product of the selected slot amplitudes on the real F.rows, with the source's masks, orientations and external heights.
2. Moments/DetectorDictionaryFiber.lean, **fiber_plain_energy_eq**: for the original row-data, mask/coprimality and U>0 hypotheses, proves the exact equality of sum_{u in F.rows}|P_j(u)*P_k(u)*W(u)|² with sum_{u in F.rows}|detectorPositiveRow(u)|².
3. Moments/DetectorPlainFiberSource.lean, **detector_row_eq_source**: EACH detector row equals

       detectorPositiveRow(u) =
         D_U^(-1/2) * sum_{I in finiteColumns(fiberPool selected)}
             fiberCoefficient(F,eta,selected,j,k,sigma,t,I)
               * rowWeight(eta,fixedBadMask,u,I),

   where D_U=(U^F.m)*(U^F.m)*product_{s in selected} U^(F.widths s).

4. Moments/DetectorPlainFiberSource.lean, detector_positive_energy_le_source and fiber_plain_energy_le_source: the original row energy is controlled by the restricted source-energy estimate. This is where extra source covariance control could improve an input.
5. Detector/DetectorPlainMarkedFineField.lean, source_batch_plain_marked_fine: proves the original C*(1+height)^J*U^(1+D.t) moment bound for j+k<=2 under actual marked capacity.
6. Detector/FinalAssemblyCertifiedBands.lean, source_moments: gathers marked, inverse and unmarked estimates into SourceMomentBound for the final analytic detector.

This supplies a TRUE, ALREADY-PROVED **moment-level source identification in OpenAI**. We do not need to invent an ideal-source lift from scratch. The remaining repository-integration task is applying the new RH_Lean NNS identity directly to these exact OAI declaration types, with actual coefficients and all hypotheses (not yet a shared imported Lean theorem).

Let c_{u,I}=fiberCoefficient(F,...,I)*rowWeight(u,I). Since the physical slot product W is ALREADY internalized in c via the original tuple pool and window, the exact marked moment after the upstream equality is

    M_jk(U)=D_U^(-1)*sum_{u in F.rows}|sum_I c_{u,I}|².

NNS simultaneously gives, with Phi(c_{u,I})=(x_{u,I},y_{u,I}) and external weight 1/D_U,

    C_all = (1/(2*D_U))*sum_{u,I,J}
             [Co0(x_{u,I},x_{u,J})+Co0(y_{u,I},y_{u,J})],

    V_all = (1/(2*D_U))*sum_{u,I,J}
             [Div0(x_{u,I},x_{u,J})+Div0(y_{u,I},y_{u,J})],

    *** M_jk(U)=C_all-V_all. ***

The diagonal is D=(1/D_U)*sum_{u,I}|c_{u,I}|², so C_all=D+C_off and

    *** M_jk(U)=D+C_off-V_off. ***

This is *exactly the same source moment OpenAI bounds*, in NNS covariance currency. It is unnormalized by the number of rows and preserves every selected mask, actual ideal phase and marked coefficient.

**IMPORTANT NO DOUBLE COUNT:** Two equivalent expressions place W in different locations.
- Raw coordinate: M_jk=sum_u |W(u)|² |P_j(u)P_k(u)|².
- Original OpenAI finite-column coordinate: M_jk=D_U^(-1)*sum_u|sum_I c_{u,I}|², where c ALREADY includes W. Multiplying this second expression by |W(u)|² a second time would be wrong.

The native theorem vf919NormalizedColumnSource_NNSCovariance in research/VF_919_ACTUAL_WEIGHTED_NNS_COVARIANCE_KERNEL_20261021.lean matches the SECOND form, while vf919ActualMarkedMoment_eq_exactWeightedNNSCovariance matches the FIRST form under a visible atom equality hypothesis.

## C. Simultaneous analytical bottleneck with OpenAI's existing proof

Put

    NetNNSPayment(U)=V_off(U)-C_off(U).

Then the unaltered actual marked estimate is

    M_jk(U)=D(U)-NetNNSPayment(U)
           <= C(1+height)^J U^(1+D.t).

The ONLY potential new improvement is an INDEPENDENT estimate on the ACTUAL original compensated ideal coefficients and their signed covariance which shows, for fixed sigma>0,

    NetNNSPayment(U) >= D(U)-C'(1+height)^J U^(1+D.t-sigma).

After the identity this is equivalent to a sharper marked estimate, so it cannot be derived circularly from the already-proved bound and recycled. The arithmetic gain must come from OpenAI's actual compensationSubsetCoefficient and source rescaling, followed by uniform source-energy/character-moment control including all resonant and nonresonant contributions.

The parent/subset matching itself is NOT an unexplained PNT independence assumption. The actual source has character-dependent phases, varying selected windows and dyadic/coprime masks. Complete uniform six-root averaging gives no automatic L2 reduction. NNS is the EXACT diagnostic for favorable cross-subset alignment, but the signed magnitude estimate remains a separate analytic theorem.

The upstream source_batch_plain_marked_fine proof has state.width=1+D.t/4 and stageError=D.t/4 and rounds its exponent to 1+D.t. This distinct published slack may be reusable but is not by itself a new 7/8 proof. Any saving must survive source_moments, other inverse/unmarked rows, the high-row geometry and the zero detector.

**Research status:** OpenAI compensation and moments: already certified upstream. RH_Lean Co-minus-Div conversion: finite identity with pinned original weights, warning-fatal Lean CI required on PR head. New fixed power saving / tracker improvement: OPEN.
