import RHLean.AlpogeProofAdapter

/-!
# Joint RHLean / Alpoge certificate audit
All commands below are kernel queries, not assertions about proof status.
Script check_axioms.py rejects custom, sorry, native_decide and any
unrecognized assumption used by any new terminal theorem.
-/

#check RHLean.AlpogeInterface.originalAlpoge_proves_RHLean_RH
#check RHLean.AlpogeInterface.originalAlpoge_proves_RHLean_DirichletHalf
#check RHLean.AlpogeInterface.gz_eq_upstream_Alpoge_Gz
#check RHLean.AlpogeInterface.originalAlpoge_RH_and_nativeGz

#print axioms RHLean.AlpogeInterface.originalAlpoge_proves_RHLean_RH
#print axioms RHLean.AlpogeInterface.originalAlpoge_proves_RHLean_DirichletHalf
#print axioms RHLean.AlpogeInterface.originalAlpoge_RH_and_nativeGz
