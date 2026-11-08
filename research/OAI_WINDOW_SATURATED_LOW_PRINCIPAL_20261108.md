# New OAI LOW-to-principal exponent gain from the unchanged HIGH window constraint

Date: 2026-11-08. Proof head: draft PR (CI evidence required).

## Original complete source and consumer (UNCHANGED)

This follows the already-compiled source-faithful OAI replay, its full
compensated total-slot-mass LOW proof, the pinned openai/math HECKE moments,
its fixed tilted HIGH supplier, and the original principal-signal contradiction.

For the **same physical source**, the original completed probe at

    x=17/48-24*h, y=23/48+12*h

has

    LOW power       L(h)=(5*x+y)/12=3/16-9*h,
    signal shift    g(h)=-11/16-8*h,
    LOW threshold   L(h)-g(h)=7/8-h.

The original anchored HIGH remainder is

    O(Z^(beta-11/16-8*h-sigma)),

so the signal comparison gives a zero boundary

    beta <= max(7/8-h,7/8-sigma)

whenever all established source/admissibility hypotheses hold.

The Nov 7 total-mass endpoint chose h=sigma=m/4 with the actual slot minimum
m=actualSlotMinimum D. This was a completed strict improvement over the
previous m/24 LOW-first gate, but it left unused window reserve.

## Exact original window budget

The original pinned OAI HighData has

    sigma+e <= (7/8)*((7/8)*rmin),

where e>0 is the original detector error, not an invented free parameter.

The existing RH_Lean `sourceWithExactSlotMinimum` calibration proves

    (7/8)*rmin=m,

without changing the actual slot list or original physical masks.
The unchanged `cappedHighData_bounds` establishes

    e <= m/4.

Therefore set the NEW legal reserve to

    sigma_win = (7/8)*m-e >= (5/8)*m.

The same actual detector error e, slot weights, the same fixed original
physical scales, compensated marked/unmarked masks, LOW exponent, and
principal normalizer are preserved. The *only* changed HighData field is
sigma. The window budget now holds with equality.

All other HIGH fields must be re-proved, not asserted:

- geometric_budget: sigma_win+8e+t/8<=63/800;
- principal_budget: sigma_win+t/8<=17/48000;
- window_budget: sigma_win+e=(7/8)*m;
- floor_budget: 2t+26e+(N+8)eps+t+t/6+t/8+sigma_win<=7/1200;
- high_saving: sigma_win+t/4<=t.

These follow from the previously proved same-source facts
    m<=t/200, e<=t/2000, (N+8)eps<=t, 0<t<=10^-8,
and the explicit positive-error budget. No new analytic moment is assumed.

Likewise the new actual tilt h=sigma_win satisfies
    0<h<1/960, 24h<t,
as required by the original complete LOW and anchored HIGH source.

Hence the existing complete theorem
    native_beta_le_total_mass_boundary
with that newly certified HighData implies

    beta <= 7/8 - sigma_win = 7/8 - (7/8)*m + e,
    beta <= 7/8 - (5/8)*m.

The improvement on the **same fixed original slot population** relative
to Nov 7 is at least

    (5/8-1/4)*m=3*m/8.

## Concrete explicit original source consequence

The already-constructed fixed source
`exists_explicit_high_data_fine` proves

    m >= 1/(12*N_*), N_* = explicitSlotCount > 0.

If the new kernel check passes, the explicit headline becomes

    beta <= 7/8 - 5/(96*N_*),

compared with the previous complete total-mass result

    beta <= 7/8 - 1/(48*N_*) = 7/8 - 2/(96*N_*).

The saving is 2.5 times the previous explicit saving; difference
    3/(96*N_*)=1/(32*N_*).

The existing native zeta-to-Hecke and Mertens converse directly give

    MertensGrowthAtMost (7/8 - 5/(96*N_*)).

No RH claim or improved-than-1/2 Mertens bound is asserted.

## Quantifier and failure audit

- Sigma is fixed before the source F, character, height, and Z.
- The source uses the *same* original ell, N, t, rmin, e and moment inputs,
  not an auxiliary hypothetical signed estimate. The only HighData
  field modified after capping is sigma.
- The original LOW and HIGH are evaluated at the *same* physical tilt and
  normalizer; moving either alone would invalidate the proof.
- The high window allowance is a pointwise **non-strict** constraint,
  so saturating it does not invalidate any strict `htiltCut` or geometric
  condition (each is verified independently).
- The original refined signed NNS moments and all downstream HIGH transport
  terms remain as compiled. This proof changes their **consumer**, not
  the moments or selected/unselected phases.
- The improvement follows on full true Hecke source, not by assuming
  OAI admissibility of the sharp 2ab far-tail cutoff.
- No PR should merge until pinned-source, warnings-fatal Lean and axiom
  closure pass, and the theorem assumptions match the public contracts.

## Future optimization (not claimed by this theorem)

Only the positive detector e prevents sigma from reaching 7m/8 exactly.
A further monotone cap e'<=e and a limiting argument might recover
more, but it changes an original detector parameter and must be audited
as a separate complete source construction, not inferred in this PR.
