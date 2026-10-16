import csv, math, statistics as st
rows=[r for r in csv.DictReader(open('ledger5000.csv'))]
D={int(r['R']):{k:float(v) for k,v in r.items()} for r in rows}
ev=[R for R in range(1000,5001)]
viol=sum(D[R]['eta_min_viol']+D[R]['eta_max_viol'] for R in ev)
brk=sum(1 for R in ev if not (D[R]['brlo']-1e-9<=D[R]['rho']<=D[R]['brhi']+1e-9))
Delta=[D[R]['Delta'] for R in ev]; Pred=[D[R]['Pred'] for R in ev]; rho=[D[R]['rho'] for R in ev]
def corr(a,b):
    ma,mb=st.mean(a),st.mean(b); sa=math.sqrt(sum((x-ma)**2 for x in a)); sb=math.sqrt(sum((y-mb)**2 for y in b))
    return sum((x-ma)*(y-mb) for x,y in zip(a,b))/(sa*sb)
print('P1a per-tag bracket violations:',int(viol))
print('P1b rho outside summed bracket:',brk)
print('P1c std(rho)/std(Pred)=%.4f corr(Delta,Pred)=%.5f'%(st.pstdev(rho)/st.pstdev(Pred),corr(Delta,Pred)))
print('    mean rho=%.3f std rho=%.3f std Pred=%.3f std Delta=%.3f'%(st.mean(rho),st.pstdev(rho),st.pstdev(Pred),st.pstdev(Delta)))
# rho normalized by R/log^2 R
rn=[D[R]['rho']/(R/math.log(R)**2) for R in ev]; print('    rho/(R/log^2R): min %.3f max %.3f'%(min(rn),max(rn)))
L=[D[R]['L'] for R in ev]
print('D1 fraction |Delta|>|L|: %.3f'%(sum(1 for d,l in zip(Delta,L) if abs(d)>abs(l))/len(ev)))
print('D2 max |Delta|/(R log R): %.4f at R=%d'%max((abs(D[R]['Delta'])/(R*math.log(R)),R) for R in ev))
print('   max |Delta|/|L|: %.2f at R=%d'%max((abs(D[R]['Delta'])/max(abs(D[R]['L']),1e-9),R) for R in ev))
print('   max |Pred|/ (R^1.5/log^2 R): %.3f'%max(abs(D[R]['Pred'])/(R**1.5/math.log(R)**2) for R in ev))
print('cons: max|checkL|=%.3e'%max(abs(D[R]['check_L']) for R in range(6,5001)))
print('cut identity: max|Bdev-cutmode|=%.3e'%max(abs(D[R]['Bdev']-D[R]['cutmode']) for R in range(6,5001)))
Bd=[D[R]['Bdev'] for R in ev]; me3=[-D[R]['eps_x3'] for R in ev]
print('P2 corr(Bdev,-eps(x/3))=%.5f ; std ratio std(Bdev+eps(x/3))/std(Bdev)=%.4f'%(corr(Bd,me3), st.pstdev([b-m for b,m in zip(Bd,me3)])/st.pstdev(Bd)))
Ad=[D[R]['Adev'] for R in ev]; ea=[-D[R]['eps_x']+D[R]['eps_x3'] for R in ev]
print('   corr(Adev, -eps(x)+eps(x/3))=%.5f'%corr(Ad,ea))
for R in [1000,2000,2500,3000,3162,4096,4999,5000]:
    d=D[R]; print(R,'L=%.2f Delta=%.2f Pred=%.2f rho=%.2f  A=%.1f B=%.1f Bdev=%.2f -eps(x/3)=%.2f  S1=%.1f S2=%.1f S3=%.1f'%(d['L'],d['Delta'],d['Pred'],d['rho'],d['S4'],d['S1']+d['S2']+d['S3'],d['Bdev'],-d['eps_x3'],d['S1'],d['S2'],d['S3']))
