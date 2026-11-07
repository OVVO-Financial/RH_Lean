#!/usr/bin/env python3
"""Generate source-pinned parallel analytic proofs, preserving original modules.
Every transformed proof is kernel-compiled by run.sh. This generator does not
certify a theorem, modify an upstream file, or replace an analytic premise.
"""
from pathlib import Path
import argparse, hashlib, json, re, subprocess

PIN = '1581d4cbdd69a0faf34b2089614fe2a814316a6a'
PREFIX = 'OAI.NumberTheory.DirichletL.Energy.'
OUT_PREFIX = 'research.oai_434.Feedback.'
MODULES = '''FirstSourceParameters DeletedRobustGeometry ReferenceRobustDeletedEnergy
ReferenceRobustOriginal ReferenceRobustPower ReferenceRobustBounded
ReferenceLivePower ReferenceLiveBounded OriginalHighReflectionGeometry
OriginalHighReflectionDeleted OriginalHighReflectionOriginal
OriginalHighReflectionPower OriginalHighReflectionBounded
OriginalHighReflectionSymmetric OriginalHighReflectionSymmetricBounded
PositiveHighSource PositiveHighParameters PositiveBalancedAdmission
PositiveHighSourceBounded PositiveHighAssembly PositiveHighAssemblyBounded
PositiveHighBound PositiveHighSourceBound NaturalLowPhysical NaturalLowStage
CappedLowStage PositiveHighPhysical NaturalHighStage ZeroGrowthPhysical
NaturalZeroStage CappedAnalyticSuccessor CertifiedExistence'''.split()


def u(s):
    return re.sub(r'\\u([0-9a-fA-F]{4})', lambda m: chr(int(m[1], 16)), s)


def once(text, old, new, label=''):
    n = text.count(old)
    if n != 1:
        raise ValueError(f'{label}: expected exactly one replacement, found {n}: {old[:130]!r}')
    return text.replace(old, new, 1)


def relax_floor(t):
    # Change only lower-bound hypotheses, never arithmetic 3/4 exponents.
    pattern = u(r'(?:\(3\s*/\s*4\s*:\s*\u211d\)|3\s*/\s*4)\s*\u2264\s*(\u03ba|kappa)')
    return re.sub(pattern, lambda m: 'RHLeanFeedback.kappaFloor' + u(r'\u2264') + m[1], t)


def coupled(width, kappa, xi, defect):
    return f'(6*{kappa}-1)*{xi}+(6*{kappa}+1)*{defect}' + u(r'\u2264') + f'(6*{kappa}-3)*{width}/6'


def make_geometry(src):
    text = (src/'LiveClippingDefect.lean').read_text()
    a=text.index('theorem robust_deleted_reference_cases ')
    b=text.index('\ntheorem robust_deleted_reference_window ',a)
    body=text[a:b]
    body=relax_floor(body)
    body=once(body, '  dsimp only\n', '  dsimp only\n  have hfeedbackFloor := RHLeanFeedback.kappaFloor_gt\n', 'geometry fact')
    body=once(body,u(r'\u03be+11*e/7 \u2264 M/14'),coupled('M',u(r'\u03ba'),u(r'\u03be'),'e'),'geometry reserve')
    body=body.replace(u(r'16*M/21+\u03be+4*e/7'),'5*M/6')
    body=body.replace(u(r'13*M/14+\u03be+11*e/7'),'M')
    old=body[body.index(u(r'    obtain \u27e8hellbound, hslot\u27e9')):]
    new=u(r'''    have hkp := RHLeanFeedback.kappa_gt h\u03ba
    have hbudget := RHLeanFeedback.parent_slot_budget M
      (Real.logb Z (X\u2081*X\u2082)) ell \u03ba e hlarge (by nlinarith only [hcap])
    have hsmall := RHLeanFeedback.retained_slot_gate_of_reserve M ell \u03ba \u03be e
      hkp hbudget hreserve
    exact RHLeanFeedback.reflected_low_of_retained_slot M _ _ ell z \u03ba \u03be e reflected
      hM hshort hz hze (by linarith) h\u03be he hsmall hbudget
      (by rw [\u2190 CenteredMomentEnergyReferenceLowBranchGeometry.length_eq_max_log Z _ hZ hlongpos]
          exact lt_of_not_ge hlo) href
''')
    body=once(body,old,new,'geometry reflected branch')
    header=u(r'''import research.oai_434.Feedback.Range
import OAI.NumberTheory.DirichletL.Energy.LiveClippingDefect

namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.RHLeanFeedbackGeometry
open HeckeFamily CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDeletionBudget
open CenteredMomentEnergyReferenceDeletionCapacity
local notation "O" => HeckeFamily.O
variable [cfg : RHLeanFeedback.KappaRange]
include cfg

theorem robust_balanced_long_nonneg (M total ell kappa xi defect : \u211d)
    (hM : 0 \u2264 M) (hell : 0 \u2264 ell)
    (hk : RHLeanFeedback.kappaFloor \u2264 kappa) (hxi : 0 \u2264 xi)
    (hlarge : 5*M/6-defect \u2264 total+ell)
    (hcap : total+ell+(6*kappa-1)*ell \u2264 M)
    (hreserve : (6*kappa-1)*xi+(6*kappa+1)*defect \u2264 (6*kappa-3)*M/6) :
    M/2 \u2264 total \u2227 0 \u2264 total-M/4 := by
  have hbudget := RHLeanFeedback.parent_slot_budget M total ell kappa defect hlarge
    (by nlinarith only [hcap])
  have hsmall := RHLeanFeedback.retained_slot_gate_of_reserve M ell kappa xi defect
    (RHLeanFeedback.kappa_gt hk) hbudget hreserve
  constructor <;> linarith

''')
    return header+body+'\nend SevenEighths.RHLeanFeedbackGeometry\nend\nend OAI\n'


def modify(name,t):
    K=u(r'\u03ba')
    t=t.replace(u(r'xi+11*defect/7\u2264s.width/14'),coupled('s.width',K,'xi','defect'))
    t=t.replace(u(r'xi+11*e/7\u2264s.width/14'),coupled('s.width',K,'xi','e'))
    if name in ['OriginalHighReflectionGeometry','OriginalHighReflectionDeleted','OriginalHighReflectionOriginal']:
        t=t.replace(u(r'xi\u2264s.width/14'),f'(6*{K}-1)*xi'+u(r'\u2264')+f'(6*{K}-3)*s.width/6')
    if name == 'DeletedRobustGeometry':
        t=t.replace('have hb := robust_balanced_long_nonneg','have hb := RHLeanFeedbackGeometry.robust_balanced_long_nonneg')
        t=t.replace('rcases robust_deleted_reference_cases','rcases RHLeanFeedbackGeometry.robust_deleted_reference_cases')
        a=t.index('    have hh := robust_reflected_low_admissible')
        b=t.index('\n\nend ',a)
        t=t[:a]+u(r'    simpa only [hd\u2081.2.2] using hc.2')+t[b:]
    if name == 'OriginalHighReflectionGeometry':
        t=t.replace(':=slot_budgets ',':=RHLeanFeedback.slot_budgets_no_defect ')
        a=t.index(u(r'  \u00b7 obtain \u27e8he,hbudget\u27e9'))
        b=t.index('\n\nend ',a)
        new=u(r'''  \u00b7 have hbudget := RHLeanFeedback.parent_slot_budget s.width
      (length Z X\u2081+length Z X\u2082) ell \u03ba 0 (by simpa using hlarge) hcap
    have hsmall := RHLeanFeedback.retained_slot_gate_of_reserve s.width ell \u03ba xi 0
      (RHLeanFeedback.kappa_gt h\u03ba) hbudget (by simpa using hxiM)
    have hlow := RHLeanFeedback.reflected_low_of_retained_slot s.width
      (length Z (X\u2081/((\u220fP\u2208D\u2081,P).absNorm:\u211d)))
      (Real.logb Z (X\u2082/((\u220fP\u2208D\u2082,P).absNorm:\u211d))) ell z \u03ba xi 0
      (max 0 (s.width-Real.logb Z (X\u2082/((\u220fP\u2208D\u2082,P).absNorm:\u211d))+xi))
      hM.le (hd\u2081.trans hshort) hz hze (by have hh := RHLeanFeedback.kappa_gt h\u03ba; linarith)
      hxi (by norm_num) hsmall hbudget
      (by rw [\u2190length_eq_max_log Z _ hZ hp\u2082]; exact lt_of_not_ge hd) le_rfl
    exact Or.inr hlow.2
''')
        t=t[:a]+new+t[b:]
    powers=['ReferenceRobustPower','ReferenceRobustBounded','OriginalHighReflectionPower','OriginalHighReflectionBounded']
    if name in powers:
        reserve='exists_bounded_separated_reference_reserve' if name.endswith('Bounded') else 'exists_reference_reserve'
        old=reserve+u(r' rho \u03b5 Mcap Bmask b\u03a6 hrho h\u03b5 hM hBmask')
        new=reserve+u(r' (100*RHLeanFeedback.allowance rho) \u03b5 Mcap Bmask b\u03a6 (by positivity) h\u03b5 hM hBmask')
        t=once(t,old,new,name+' reserve constructor')
        marker='  obtain '+u(r'\u27e8d,xi,saving,L,Cscalar')
        t=once(t,marker,'  have hallowance := RHLeanFeedback.allowance_pos rho hrho\n'+marker,name)
        ref=u(r'  refine \u27e8d,xi,L,hd,hxi,hxirho,hL,')
        t=once(t,ref,u(r'''  have hxiAllowance : xi \u2264 RHLeanFeedback.allowance rho := by nlinarith only [hxirho]
  have hallowanceCap := RHLeanFeedback.allowance_le rho hrho.le
  have hxirho' : xi \u2264 rho/100 := hxiAllowance.trans hallowanceCap
''')+ref.replace('hxirho,',"hxirho',"),name)
        if name.endswith('Bounded'):
            t=once(t,"  refine "+u(r'\u27e8d,xi,L,hd,hxi,hxirho\u0027,hL,hLupper,'),
                u(r'''  have hLupper' : L \u2264 Mcap+Bmask+rho/100 := by nlinarith only [hLupper,hallowanceCap]
  refine \u27e8d,xi,L,hd,hxi,hxirho',hL,hLupper','''),name+' length cap')
        a=t.index('  have hxiM:')
        b=t.index('\n  have hh:=',a)
        defect='RHLeanFeedback.allowance rho' if name.startswith('Reference') else '0'
        new=f'  have hxiM := RHLeanFeedback.uniform_reserve rho {K} s.width xi ({defect})\n'
        new+='    hrho h'+K+' hslo hxi.le '+('(by positivity)' if defect=='0' else 'hallowance.le')
        new+=' hxiAllowance '+('(by positivity)' if defect=='0' else 'le_rfl')+'\n'
        if defect=='0':
            new+='  simp only [mul_zero, add_zero] at hxiM\n'
        t=t[:a]+new.rstrip()+t[b:]
        if name.startswith('Reference'):
            t=t.replace('5*s.width/6-rho/100','5*s.width/6-RHLeanFeedback.allowance rho')
            t=t.replace('(rho/100)','(RHLeanFeedback.allowance rho)')
            a=t.index('  have hg:=CenteredMomentEnergyLiveClippingDefect.robust_slot_budgets')
            b=t.index('\n  have hledger:=',a)
            t=t[:a]+u(r'''  have hbudget := RHLeanFeedback.parent_slot_budget s.width
    (Real.logb Z (X\u2081*X\u2082)) (\u2211i,w i) \u03ba (RHLeanFeedback.allowance rho)
    hlarge (by nlinarith only [hcap])
  have hsmall := RHLeanFeedback.retained_slot_gate_of_reserve s.width (\u2211i,w i) \u03ba xi
    (RHLeanFeedback.allowance rho) (RHLeanFeedback.kappa_gt h\u03ba) hbudget hxiM
  have hsumcap:(\u2211i,w i)\u2264Mcap:=by linarith [s.width_nonneg]
''').rstrip()+t[b:]
    if name in ['ReferenceLivePower','ReferenceLiveBounded']:
        t=t.replace('(rho/100)','(RHLeanFeedback.allowance rho)')
        marker='  obtain '+u(r'\u27e8Z\u2080,hZ\u2080,hendpoint\u27e9')
        t=once(t,marker,'  have hallowance := RHLeanFeedback.allowance_pos rho hrho\n'+marker,name)
    return t


def generate(root, upstream):
    src=upstream/'OAI/NumberTheory/DirichletL/Energy'
    out=root/'research/oai_434/Feedback'
    out.mkdir(parents=True,exist_ok=True)
    (out/'Geometry.lean').write_text(make_geometry(src))
    texts={m:(src/(m+'.lean')).read_text() for m in MODULES}
    ns={re.search(r'^namespace SevenEighths\.(\w+)',v,re.M)[1] for v in texts.values()}
    mapping={n:'Feedback'+n for n in ns}
    name_pattern=re.compile(r'\b('+'|'.join(sorted(mapping,key=len,reverse=True))+r')\b')
    manifest=[]
    for name,original in texts.items():
        t=modify(name,original)
        t=relax_floor(t)
        for dep in MODULES:
            t=t.replace('import '+PREFIX+dep+'\n','import '+OUT_PREFIX+dep+'\n')
        t=name_pattern.sub(lambda m:mapping[m[0]],t)
        t='import research.oai_434.Feedback.Geometry\n'+t
        t=re.sub(r'(^namespace SevenEighths\.\w+\n)',r'\1variable [cfg : RHLeanFeedback.KappaRange]\ninclude cfg\n',t,count=1,flags=re.M)
        t=re.sub(r'((?:^theorem |^lemma )[\s\S]*?:=\s*by)\n',
                 r'\1\n  have hfeedbackFloor := RHLeanFeedback.kappaFloor_gt\n',t,flags=re.M)
        if re.search(r'\b(sorry|admit|axiom)\b',re.sub(r'/\-[\s\S]*?\-/','',t)):
            raise ValueError('Forbidden proof token in '+name)
        (out/(name+'.lean')).write_text(t)
        manifest.append({'module':OUT_PREFIX+name,'original_module':PREFIX+name,
            'original_sha256':hashlib.sha256(original.encode()).hexdigest(),
            'generated_sha256':hashlib.sha256(t.encode()).hexdigest()})
    original=(src/'CertifiedExistence.lean').read_text()
    start=original.index('theorem terminal_certificate ')
    end=original.index(':=by',start)
    signature=original[start:end].replace('theorem terminal_certificate ', 'theorem terminal_certificate_half ')
    signature=once(signature,u(r'(h\u03ba0:(3/4:\u211d)\u2264\u03ba)'),u(r'(h\u03ba0:(1/2:\u211d)<\u03ba)'), 'explicit half-range')
    header=original[:original.index('theorem certified_bands ')]
    header=header.replace('import '+PREFIX+'CappedAnalyticSuccessor','import '+OUT_PREFIX+'CertifiedExistence')
    header=header.replace('namespace SevenEighths.CenteredMomentEnergyCertifiedExistence','namespace SevenEighths.RetainedSlotFeedback')
    proof=u(r''' := by
  letI : RHLeanFeedback.KappaRange := { lower := \u03ba, lower_gt_half := h\u03ba0 }
  exact FeedbackCenteredMomentEnergyCertifiedExistence.terminal_certificate
    (\u03b1:=\u03b1) M H hH W aslot bslot a b radial Bmask L lo hi Mcap \u03ba \u03b5
    haslot hWs hW hbslot ha haUpper hb _hrad hmask hMcap le_rfl h\u03b5 hbeta h\u03ba

#print axioms terminal_certificate_half
#check terminal_certificate_half
end SevenEighths.RetainedSlotFeedback
end
end OAI
''')
    (out/'Terminal.lean').write_text(header+signature+proof)
    corrections=root/'scripts/lean/retained_slot_feedback/corrections.json'
    if corrections.exists():
        for module, patches in json.loads(corrections.read_text()).items():
            dest=out/(module+'.lean')
            value=dest.read_text()
            for change in patches:
                value=once(value,change['old'],change['new'],module+' reviewed correction')
            dest.write_text(value)
    for item in manifest:
        dest=out/(item['module'].split('.')[-1]+'.lean')
        item['generated_sha256']=hashlib.sha256(dest.read_bytes()).hexdigest()
    sources={p.stem:p for p in out.glob('*.lean')}
    order=[];active=set();seen=set()
    def visit(name):
        if name in seen:return
        if name in active:raise ValueError('Import cycle '+name)
        active.add(name)
        for dep in re.findall(r'^import research\.oai_434\.Feedback\.(\w+)',sources[name].read_text(),re.M):
            if dep not in sources:raise ValueError('Missing generated module '+dep)
            visit(dep)
        active.remove(name);seen.add(name);order.append(name)
    for name in sources:visit(name)
    data={'original_pin':PIN,'uniformity':'fixed KappaRange chosen before analytic constants',
          'generated':manifest,'compile_order':order,'scope':'No new global Mertens exponent asserted'}
    (root/'retained-slot-generation.json').write_text(json.dumps(data,indent=2))
    return data


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path.cwd());ap.add_argument('--upstream',type=Path)
    ap.add_argument('--source-only',action='store_true',help='Generate from an already verified source-only artifact; never compiles Lean.')
    args=ap.parse_args();up=args.upstream or args.root/'oai-upstream/lean'
    if not args.source_only:
        actual=subprocess.check_output(['git','-C',str(up.parent),'rev-parse','HEAD'],text=True).strip()
        if actual!=PIN:raise SystemExit('Original OAI pin mismatch: '+actual)
    data=generate(args.root,up)
    print('Generated',len(data['generated']),'parallel analytic modules; original files unchanged.')
    print(' '.join(data['compile_order']))
if __name__=='__main__':main()
