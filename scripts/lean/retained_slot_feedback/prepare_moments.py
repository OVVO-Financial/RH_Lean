#!/usr/bin/env python3
"""Assemble all four source moments and the immediate marked row-count consumer."""
from pathlib import Path
import argparse,json,hashlib
from prepare import u, once


def generate(root,upstream):
    base=upstream/'OAI/NumberTheory/DirichletL';out=root/'research/oai_434/Feedback'
    original=(base/'Detector/FinalAssemblyCertifiedBands.lean').read_text()
    inp=(base/'Detector/FinalAssemblyMomentInput.lean').read_text()
    header=original[:original.index('def detectorMesh ')]
    header='import research.oai_434.Feedback.SourceFeedback\n'+header
    header=header.replace('namespace SevenEighths.ProbeFinalAssemblyCertifiedBands',
        'namespace SevenEighths.RetainedSlotMoments\nopen ProbePhysical RetainedSlotDetector FeedbackDetectorPlainMarkedFineField')
    header=header.replace('open ProbeDetectorPlainMarkedFineField ProbeDetectorPlainUnmarkedField',
        'open ProbeDetectorPlainUnmarkedField')
    a=inp.index('def SourceMomentBound ');b=inp.index('\nlemma SourceMomentBound.',a)
    definition=inp[a:b].replace('def SourceMomentBound ', 'def SourceMomentBoundAtKappa ')
    definition=once(definition,u(r'(counts : CountParameters F.modulus \u22a4 D.t) (\u03b7 : Character)'),
        u(r'(counts : CountParameters F.modulus \u22a4 D.t) (kappa : \u211d) (\u03b7 : Character)'),'moment input parameter')
    definition=once(definition,u(r'D.t D.t i z \u0394'),u(r'D.t D.t i z ((kappa-3/4)/2)'),'capacity index')
    a=original.index('theorem source_moments ');b=original.index('\ntheorem fine_moments_of_certified',a)
    body=original[a:b].replace('theorem source_moments ', 'theorem source_moments_at_kappa ')
    body=once(body,u(r'(counts:CountParameters F.modulus \u22a4 D.t)(mesh:\u211d)'),
        u(r'(counts:CountParameters F.modulus \u22a4 D.t)(kappa mesh:\u211d)'),'assembly parameter')
    body=body.replace('PositiveFineSourceInput F mesh','PositiveFineSourceInputAt F mesh kappa')
    body=body.replace(u(r'SourceMomentBound F counts \u03b7'),u(r'SourceMomentBoundAtKappa F counts kappa \u03b7'))
    body=body.replace('source_batch_plain_marked_fine F mesh',
        'FeedbackDetectorPlainMarkedFineField.source_batch_plain_marked_fine_at F kappa mesh')
    a=body.index(u(r'  \u00b7 intro selected hselected hcap j k hjk'))
    b=body.index(u(r'  \u00b7 intro j k hjk'),a)
    body=body[:a]+u(r'''  \u00b7 intro selected hselected hcap j k hjk \u03c3 h\u03c3 t ht
    have heq : (3/4+2*((kappa-3/4)/2) : \u211d) = kappa := by ring
    rw [heq] at hcap
    have hUone : 1 \u2264 Z^d := (source_base_gt_one D Z d hi.1 hd).le
    have hpow : (Z^d)^(1+D.t/2) \u2264 (Z^d)^(1+D.t) :=
      Real.rpow_le_rpow_of_exponent_le hUone (by linarith [D.t_pos])
    have hb := (hmarked selected hselected hcap j k hjk \u03c3 h\u03c3 t ht).trans
      (mul_le_mul_of_nonneg_left hpow (show 0 \u2264 Cm*(1+height)^Jm by positivity))
    exact hb.trans (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU _))
''')+body[b:]
    wrapper=u(r'''theorem source_moments_half {\u0394 : \u211d} {D : HighData \u0394}
    (F : SourceData D) (counts : CountParameters F.modulus \u22a4 D.t)
    (kappa : \u211d) (hk : 1/2 < kappa)
    (hbeta : (51/100 : \u211d) \u2264 HeckeZeroSupremum.beta)
    (hlicense : 2*HeckeZeroSupremum.beta-1 \u2264 kappa)
    (hfine : \u2200 j, D.ell j \u2264 detectorMeshAt kappa D.t / 200) :
    \u2203 J : \u211d, 0 \u2264 J \u2227 \u2200 eta : Character, \u2203 C : \u211d, 0 < C \u2227
      \u2200 tau : \u211d, 0 < tau \u2192 tau \u2264 1 \u2192 \u2200\u1da0 Z : \u211d in atTop,
        SourceMomentBoundAtKappa F counts kappa eta Z tau
          (C*(1+Z^(2*tau))^J) (Z^(2*tau)) := by
  have hcert := source_bands_half F kappa hk hbeta hlicense
  obtain \u27e8hp, hz\u27e9 := plain_inputs_at F kappa (by linarith) hcert
  exact source_moments_at_kappa F counts kappa (detectorMeshAt kappa D.t)
    (detectorMeshAt_pos kappa D.t (by linarith) D.t_pos) hfine hp hz

#print axioms source_moments_half
#check source_moments_half
end SevenEighths.RetainedSlotMoments
end
end OAI
''')
    (out/'SourceMoments.lean').write_text(header+definition+'\n'+body+'\n'+wrapper)
    original_count=(base/'Hecke/DetectorRawBranches.lean').read_text()
    h=original_count[:original_count.index('theorem Fiber.lengths ')]
    h=h.replace('namespace SevenEighths.HeckeDetectorRawFiber','namespace SevenEighths.RetainedSlotFiberCount\nopen HeckeDetectorRawFiber')
    h='import OAI.NumberTheory/DirichletL.Hecke.DetectorRawBranches\n'.replace('NumberTheory/','NumberTheory.')+h
    a=original_count.index('theorem Fiber.plain_marked_count ');b=original_count.index('\ntheorem Fiber.plain_unmarked_count ',a)
    count=original_count[a:b].replace('theorem Fiber.plain_marked_count ','theorem plain_marked_count_half ')
    count=count.replace(u(r'{\u0394 c \u03ba C height \u03b5m : \u211d}'),u(r'{kappa c \u03ba C height \u03b5m : \u211d}'))
    count=count.replace(u(r'Moments F \u0394 c \u03ba'),u(r'Moments F ((kappa-3/4)/2) c \u03ba'))
    count=count.replace(u(r'(h\u0394 : 0\u2264\u0394)'),u(r'(hkappa : 0\u2264kappa)'))
    count=count.replace(u(r'(3/4+2*\u0394)'),'kappa')
    count=once(count,':= by\n',u(r''' := by
  have hmarked := moments.plain_marked
  have heq : (3/4+2*((kappa-3/4)/2) : \u211d) = kappa := by ring
  simp only [heq] at hmarked
'''),'count converted capacity')
    count=count.replace('hcap moments.plain_marked','hcap hmarked')
    (out/'RowCount.lean').write_text(h+count+'\n#print axioms plain_marked_count_half\nend SevenEighths.RetainedSlotFiberCount\nend\nend OAI\n')
    corrections=root/'scripts/lean/retained_slot_feedback/moment_corrections.json'
    if corrections.exists():
        for module,patches in json.loads(corrections.read_text()).items():
            path=out/(module+'.lean');text=path.read_text()
            for patch in patches:text=once(text,patch['old'],patch['new'],module+' reviewed correction')
            path.write_text(text)
    path=root/'retained-slot-generation.json';data=json.loads(path.read_text())
    for name,orig,p in [('SourceMoments',original,'Detector.FinalAssemblyCertifiedBands'),('RowCount',original_count,'Hecke.DetectorRawBranches')]:
        if name not in data['compile_order']:data['compile_order'].append(name)
        data['generated'].append({'module':'research.oai_434.Feedback.'+name,
            'original_module':'OAI.NumberTheory.DirichletL.'+p,
            'original_sha256':hashlib.sha256(orig.encode()).hexdigest(),
            'generated_sha256':hashlib.sha256((out/(name+'.lean')).read_bytes()).hexdigest()})
    template=root/'scripts/lean/retained_slot_feedback/Applications.lean'
    application=out/'Applications.lean';application.write_text(template.read_text())
    if 'Applications' not in data['compile_order']:data['compile_order'].append('Applications')
    data['generated'].append({'module':'research.oai_434.Feedback.Applications',
        'original_module':None,'generated_sha256':hashlib.sha256(application.read_bytes()).hexdigest()})
    path.write_text(json.dumps(data,indent=2))
    print('Generated complete four-field source moments and marked row-count consumer.')

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path.cwd());ap.add_argument('--upstream',type=Path)
    args=ap.parse_args();generate(args.root,args.upstream or args.root/'oai-upstream/lean')
