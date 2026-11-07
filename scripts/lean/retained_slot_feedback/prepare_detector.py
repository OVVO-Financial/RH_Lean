#!/usr/bin/env python3
"""Extend the checked analytic band into the literal detector marked moment."""
from pathlib import Path
import argparse, hashlib, json
from prepare import u, once


def generate(root,upstream):
    base=upstream/'OAI/NumberTheory/DirichletL'
    out=root/'research/oai_434/Feedback'
    original=(base/'Moments/DetectorPlainMarkedState.lean').read_text()
    header=original[:original.index('theorem source_slot_coefficient ')]
    header='import OAI.NumberTheory.DirichletL.Moments.DetectorPlainMarkedState\n'+header
    header=header.replace('namespace SevenEighths.CenteredMomentDetectorPlainMarkedState',
        'namespace SevenEighths.FeedbackDetectorPlainMarkedState\nopen CenteredMomentDetectorPlainMarkedState')
    initial=original[original.index('theorem source_batch_marked_initial '):original.index('\nend SevenEighths.')]
    initial=once(initial,'(S:ProbeFinalAssembly.SourceData D):',u(r'(S:ProbeFinalAssembly.SourceData D)(\u03ba:\u211d):'),'initial parameter')
    initial=initial.replace(u(r'(3/4+2*\u0394)'),u(r'\u03ba'))
    initial=header+initial+'\nend SevenEighths.FeedbackDetectorPlainMarkedState\nend\nend OAI\n'
    (out/'MarkedInitial.lean').write_text(initial)
    original_field=(base/'Detector/DetectorPlainMarkedFineField.lean').read_text()
    field='import research.oai_434.Feedback.MarkedInitial\n'+original_field
    field=field.replace('SevenEighths.ProbeDetectorPlainMarkedFineField','SevenEighths.FeedbackDetectorPlainMarkedFineField')
    field=field.replace('CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainMarkedState',
        'CenteredMomentDetectorEnergyInitialState FeedbackDetectorPlainMarkedState')
    field=field.replace('PositiveFineSourceInput','PositiveFineSourceInputAt')
    field=once(field,u(r'(S:SourceData D)(mesh:\u211d):Prop:='),u(r'(S:SourceData D)(mesh \u03ba:\u211d):Prop:='),'input definition')
    field=once(field,u(r'(S:SourceData D)(mesh:\u211d)(hmesh:'),u(r'(S:SourceData D)(\u03ba mesh:\u211d)(hmesh:'),'field parameter')
    field=field.replace('PositiveFineSourceInputAt S mesh)',u(r'PositiveFineSourceInputAt S mesh \u03ba)'))
    field=field.replace('(kappaPlain D)',u(r'\u03ba'))
    field=field.replace(u(r'(3/4+2*\u0394)'),u(r'\u03ba'))
    field=field.replace('source_batch_marked_initial S',u(r'source_batch_marked_initial S \u03ba'))
    field=field.replace('source_batch_plain_marked_fine','source_batch_plain_marked_fine_at')
    field=field.replace('1+D.t','1+D.t/2')
    field=once(field,'rw [hwidthstate];linarith [(fixed_parameters D).2.2.2.1]',
        'rw [hwidthstate]\n    dsimp [delta, stageError]\n    linarith','retained width')
    (out/'MarkedField.lean').write_text(field)
    original_inputs=(base/'Detector/FinalAssemblyCertifiedBands.lean').read_text()
    h=original_inputs[:original_inputs.index('def detectorMesh ')]
    h='import research.oai_434.Feedback.Terminal\nimport research.oai_434.Feedback.MarkedField\n'+h
    h=h.replace('namespace SevenEighths.ProbeFinalAssemblyCertifiedBands','namespace SevenEighths.RetainedSlotDetector')
    h=h.replace('open ProbeDetectorPlainMarkedFineField ProbeDetectorPlainUnmarkedField',
        'open FeedbackDetectorPlainMarkedFineField ProbeDetectorPlainUnmarkedField')
    setup=u(r'''def detectorMeshAt (kappa t : \u211d) : \u211d := fineMesh 2 0 1 kappa (t/4)

lemma detectorMeshAt_pos (kappa t : \u211d) (hk : 0 \u2264 kappa) (ht : 0 < t) :
    0 < detectorMeshAt kappa t := by
  exact (bounds 2 (finalSourceCap 2 0 1 (t/4)) kappa (t/4)
    (by norm_num) (sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) _) hk
    (by positivity)).2.2.2.2.1

theorem source_bands_half {\u0394 : \u211d} {D : HighData \u0394} (F : SourceData D)
    (kappa : \u211d) (hk : 1/2 < kappa)
    (hbeta : (51/100 : \u211d) \u2264 HeckeZeroSupremum.beta)
    (hlicense : 2*HeckeZeroSupremum.beta-1 \u2264 kappa)
    (bPhi : \u211d) (hbPhi : 0 < bPhi) :
    CertifiedBand (\u03b1:=Fin D.N) F.modulus \u22a4 le_top (fun x => conj (F.W x))
      2 (1/4) (9/4) bPhi 0 1 (33/50) (33/50) 2 kappa (stageError D)
      (count 2 (stageError D)) := by
  exact RetainedSlotFeedback.terminal_certificate_half (\u03b1:=Fin D.N)
    F.modulus \u22a4 le_top (fun x => conj (F.W x)) 1 2 (1/4) (9/4) bPhi 0 1
    (33/50) (33/50) 2 kappa (stageError D)
    (by norm_num) (conjugate_source_support F)
    (Complex.conjCLE.contDiff.comp (F.W.smooth \u22a4))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbPhi
    (by norm_num) (by norm_num) hk (fixed_parameters D).2.2.1 hbeta hlicense

''')
    a=original_inputs.index('theorem plain_inputs ')
    b=original_inputs.index('\ntheorem source_moments ',a)
    inp=original_inputs[a:b].replace('theorem plain_inputs ', 'theorem plain_inputs_at ')
    inp=once(inp,'(F:SourceData D)',u(r'(F:SourceData D)(\u03ba:\u211d)(h\u03ba:0\u2264\u03ba)'), 'inputs parameter')
    inp=inp.replace('(kappaPlain D)',u(r'\u03ba'))
    inp=inp.replace('detectorMesh '+u(r'\u0394')+' D.t',u(r'detectorMeshAt \u03ba D.t'))
    inp=inp.replace('PositiveFineSourceInput F '+u(r'(detectorMeshAt \u03ba D.t)'),
        'PositiveFineSourceInputAt F '+u(r'(detectorMeshAt \u03ba D.t) \u03ba'))
    inp=inp.replace('hp.2.2.2.2.2.le',u(r'h\u03ba'))
    a=field.index('theorem source_batch_plain_marked_fine_at ')
    b=field.index(':=by',a)
    sig=field[a:b].replace('source_batch_plain_marked_fine_at','source_batch_plain_marked_fine_half')
    start=sig.index(u(r'    (S:SourceData D)(\u03ba mesh:\u211d)'))
    end=sig.index(u(r'    \u2203J:'),start)
    sig=sig[:start]+u(r'''    (S:SourceData D)(\u03ba:\u211d)(hk:1/2<\u03ba)
    (hbeta:(51/100:\u211d)\u2264HeckeZeroSupremum.beta)
    (hlicense:2*HeckeZeroSupremum.beta-1\u2264\u03ba)
    (hfine:\u2200j,D.ell j\u2264detectorMeshAt \u03ba D.t/200):
''')+sig[end:]
    proof=u(r''' := by
  have hmesh := detectorMeshAt_pos \u03ba D.t (by linarith) D.t_pos
  have hcert := source_bands_half S \u03ba hk hbeta hlicense
  obtain \u27e8hp, _hz\u27e9 := plain_inputs_at S \u03ba (by linarith) hcert
  exact FeedbackDetectorPlainMarkedFineField.source_batch_plain_marked_fine_at
    S \u03ba (detectorMeshAt \u03ba D.t) hmesh hfine hp

#print axioms source_bands_half
#print axioms source_batch_plain_marked_fine_half
#check source_batch_plain_marked_fine_half
end SevenEighths.RetainedSlotDetector
end
end OAI
''')
    (out/'SourceFeedback.lean').write_text(h+setup+inp+'\n'+sig+proof)
    corrections=root/'scripts/lean/retained_slot_feedback/detector_corrections.json'
    if corrections.exists():
        for module, patches in json.loads(corrections.read_text()).items():
            dest=out/(module+'.lean');value=dest.read_text()
            for change in patches:value=once(value,change['old'],change['new'],module+' reviewed correction')
            dest.write_text(value)
    result=root/'retained-slot-generation.json';data=json.loads(result.read_text())
    for name,orig,path in [('MarkedInitial',original,'Moments/DetectorPlainMarkedState'),
                           ('MarkedField',original_field,'Detector/DetectorPlainMarkedFineField'),
                           ('SourceFeedback',original_inputs,'Detector/FinalAssemblyCertifiedBands')]:
        if name not in data['compile_order']:data['compile_order'].append(name)
        data['generated'].append({'module':'research.oai_434.Feedback.'+name,
            'original_module':'OAI.NumberTheory.DirichletL.'+path.replace('/','.'),
            'original_sha256':hashlib.sha256(orig.encode()).hexdigest(),
            'generated_sha256':hashlib.sha256((out/(name+'.lean')).read_bytes()).hexdigest()})
    result.write_text(json.dumps(data,indent=2))
    print('Generated literal source feedback with original rows and 1+t/2 exponent.')

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path.cwd());ap.add_argument('--upstream',type=Path)
    args=ap.parse_args();generate(args.root,args.upstream or args.root/'oai-upstream/lean')
