#!/usr/bin/env python3
"""Exact finite Fourier conductor decomposition of 2,3,5,7 Euler product and
physical square-root endpoint samples, verifying all inverse FFT equalities."""
import json,os,math
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
O=os.path.dirname(os.path.abspath(__file__))
P=(2,3,5,7);L=math.prod(P)**2
n=np.arange(L,dtype=np.int64)
f=np.ones(L,dtype=np.int8)
for p in P:
    f[n%p==0]*=-1
    f[n%(p*p)==0]=0
mean=math.prod((1-1/p)**2 for p in P)
assert abs(f.mean()-mean)<1e-12
expected=np.empty(L+1,dtype=float);expected[0]=0
expected[1:]=np.cumsum(np.roll(f,-1),dtype=float)-np.arange(1,L+1)*mean
assert abs(expected[-1])<1e-8
hat=np.fft.fft(f)/L
freq=np.arange(L)
orders=L//np.gcd(freq,L)
qs=np.unique(orders[1:])
components=np.zeros((len(qs),L+1),dtype=np.float64)
for i,q in enumerate(qs):
    masked=np.zeros_like(hat)
    masked[orders==q]=hat[orders==q]
    recovered=np.fft.ifft(masked*L)
    assert abs(recovered.imag).max()<5e-12
    components[i,1:]=np.cumsum(np.roll(recovered.real,-1))
assert np.max(np.abs(components.sum(axis=0)-expected))<5e-8
phase_ord=np.arange(L)
phase_square=(np.arange(L,dtype=np.int64)**2-1)%L
results={}
for label,indices in [('ordinary',phase_ord),('square',phase_square)]:
    comp=components[:,indices]
    total=expected[indices]
    diag=(comp*comp).sum(axis=0)
    cross=total*total-diag
    results[label]={
      'mean_total_energy':float(np.mean(total*total)),
      'mean_conductor_diagonal_energy':float(np.mean(diag)),
      'mean_signed_cross_conductor_energy':float(np.mean(cross)),
      'cross_to_diagonal':float(np.mean(cross)/np.mean(diag)),
      'maxabs_total_prefix':float(np.max(abs(total))),
      'mean_abs_total_prefix':float(np.mean(abs(total))),
      'maxabs_cross_energy':float(np.max(abs(cross))),
    }
sq_energy=np.mean(components[:,phase_square]**2,axis=1)
ord_energy=np.mean(components[:,phase_ord]**2,axis=1)
idx=np.argsort(sq_energy)[::-1][:12]
results['top_12_conductors']=[{'q':int(qs[i]),'square_mean_energy':float(sq_energy[i]),
                             'ordinary_mean_energy':float(ord_energy[i])} for i in idx]
results['spectrum_nonzero_frequency_count']=int(np.count_nonzero(abs(hat[1:])>1e-12))
results['num_reduced_conductors']=len(qs)
results['max_fft_reconstruction_error']=float(np.max(np.abs(components.sum(axis=0)-expected)))
with open(O+'/fourier_conductor_results.json','w') as h:json.dump(results,h,indent=2)
labels=['Uniform endpoints','Square endpoints']
diag_y=[results[x]['mean_conductor_diagonal_energy'] for x in ['ordinary','square']]
cross_y=[results[x]['mean_signed_cross_conductor_energy'] for x in ['ordinary','square']]
net_y=[results[x]['mean_total_energy'] for x in ['ordinary','square']]
plt.figure(figsize=(9.5,5.5))
x=np.arange(2)
plt.bar(x-.25,diag_y,width=.25,label='Sum of conductor diagonal energies')
plt.bar(x,cross_y,width=.25,label='Signed cross-conductor contribution')
plt.bar(x+.25,net_y,width=.25,label='Resultant centered prefix energy')
plt.axhline(0,c='gray',lw=.8)
plt.xticks(x,labels);plt.ylabel('Average energy across exact 44,100 CRT root phases')
plt.title('Actual Euler product Fourier conductor Gram (primes 2,3,5,7)\nExact FFT reconstruction, no stochastic model')
plt.grid(axis='y',alpha=.2);plt.legend(fontsize=8);plt.tight_layout()
plt.savefig(O+'/euler_fourier_signed_gram.png',dpi=175);plt.close()
print(json.dumps(results,indent=2))
