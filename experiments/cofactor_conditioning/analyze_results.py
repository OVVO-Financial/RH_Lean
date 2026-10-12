from pathlib import Path
import pandas as pd
import numpy as np
D=Path(__file__).resolve().parent
f=pd.read_csv(D/'root_features.csv')
o=pd.read_csv(D/'selected_owner_groups.csv')
d=pd.read_csv(D/'selected_depth.csv')
g=pd.read_csv(D/'selected_gcd_overlap.csv')
y=pd.read_csv(D/'selected_dyadic.csv')
steps=pd.read_csv(D/'selected_prime_updates.csv')
print('All root features:',f.shape)
print('Correlation C vs features across roots 31..6000:')
z=f[f.R>=31].copy()
z['signed_extension_cancellation_ratio']=z.highprime_total_signed.abs()/z.highprime_total_abs
z['log_abs_extension']=np.log10(z.highprime_total_abs)
z['cofactor_sign_weighting_impact']=np.abs(z.conditional_covariance_correction)/z.highprime_total_abs
for nm in ['weighted_parity_mean','unweighted_parity_mean','signed_extension_cancellation_ratio','cofactor_sign_weighting_impact','log_abs_extension','sign_cdf_gap_min','sign_cdf_gap_max','highprime_total_signed','smooth_mass','conditional_covariance_correction']:
  print(f'   {nm:38s} pearson C={z.C_R.corr(z[nm]):+.5f}, Pearson |Q|={z.Q_R.abs().corr(z[nm]):+.5f}')
print('CDF crossings:',int(z.sign_cdf_crosses.sum()),'of',len(z),'first crossing root',z[z.sign_cdf_crosses==1].R.min())
print('Strong weighted parity shifts selected:')
cols=['R','Q_R','C_R','highprime_total_signed','highprime_total_abs','weighted_parity_mean','unweighted_parity_mean','independent_prediction_B','conditional_covariance_correction','smooth_mass','sign_cdf_gap_min','sign_cdf_gap_max','sign_cdf_crosses']
print(f[f.R.isin([56,317,1000,2000,5561,6000])][cols].to_string(index=False))
print('gcd cross strata:')
print(g.to_string(index=False))
print('Gram selected normalized:')
sel=f[f.R.isin([56,317,1000,2000,5561,6000])].copy()
sel['sameprime_gram_ratio']=sel.centered_owner_prime_diagonal/(sel.R**2*sel.K_R)
sel['owner_distinct_to_diagonal']=sel.owner_distinct_cross/sel.centered_owner_prime_diagonal
sel['cross_coprime_to_shared_ratio']=sel.same_prime_cross_gcd1/sel.same_prime_cross_shared.abs()
print(sel[['R','centered_owner_prime_sum','centered_owner_prime_diagonal','sameprime_gram_ratio','same_prime_cross_gcd1','same_prime_cross_shared','owner_distinct_cross','owner_distinct_to_diagonal']].to_string(index=False))
print('Owner cancellation by owner grouping:')
for r,rr in o.groupby('R'):
    jj=rr.smooth_signed+rr.highprime_signed
    sm=np.sum(abs(rr.smooth_signed)+abs(rr.highprime_signed))
    sp=np.sum(abs(jj))
    print('  R',r,'abs separate',sm,'abs net per owner',sp,'abs global',abs(jj.sum()),'owner join gain %',round(100*(1-sp/sm),2),'cross-owner gain %',round(100*(1-abs(jj.sum())/sp),3),'same owner opposite sign count',((rr.smooth_signed*rr.highprime_signed)<0).sum(),'owner count',len(rr))
    print('    largest joined owner residuals:',rr.assign(net=jj).sort_values('net',key=abs,ascending=False)[['largest_prime_owner','smooth_signed','highprime_signed','net']].head(7).values.tolist())
print('Factor-depth table:')
for r,rr in d.groupby('R'):
    print('R',r,'S by depth',dict(zip(rr.omega_depth,rr.smooth_signed)),'H by depth',dict(zip(rr.omega_depth,rr.highprime_signed)))
print('Dyadic cofactor output sample R=317:')
print(y[y.R==317].to_string(index=False))
