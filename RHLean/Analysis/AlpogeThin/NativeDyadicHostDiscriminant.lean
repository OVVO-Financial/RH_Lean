import RHLean.Analysis.AlpogeNativeDiscriminant
import RHLean.Analysis.AlpogeThin.NativeDyadicHostRaw

/-!
# Original real degree and discriminant square for the actual raw host

These are the literal `HostDer.finrank_F` and `HostDer.discr_sq` conclusions
for the already constructed native raw host, obtained from the same CM
field's degree and unramified maximal-real-subfield extension.

Source interface: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`ConjEMemHostFIff.lean`. The source archive/mirror states no license;
attribution is retained without assigning a new license.
-/

set_option autoImplicit false

noncomputable section

open NumberField

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits

theorem nativeDyadicHostRaw_finrank_F
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    Module.finrank ℚ (nativeDyadicHostRaw e q d he hH).F =
      2 * (nativeDyadicFrame e).ord := by
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hq2 : q ≠ 2 := by omega
  have hd2 : d ≠ 2 := by omega
  have hqd : q ≠ d := by omega
  have hq4 : q % 4 = 3 := by omega
  have hd4 : d % 4 = 3 := by omega
  rw [nativeDyadicFrame_ord]
  exact alpogeNativeHostReal_finrank e q d hq2 hd2 hqd hq4 hd4

theorem nativeDyadicHostRaw_discr_sq
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    discr (nativeDyadicHostRaw e q d he hH).E =
      discr (nativeDyadicHostRaw e q d he hH).F ^ 2 := by
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hq2 : q ≠ 2 := by omega
  have hd2 : d ≠ 2 := by omega
  have hqd : q ≠ d := by omega
  have hq4 : q % 4 = 3 := by omega
  have hd4 : d % 4 = 3 := by omega
  exact alpogeNativeHostField_discr_sq e q d hq2 hd2 hqd hq4 hd4

end RHLean.Analysis.AlpogeThin

end
