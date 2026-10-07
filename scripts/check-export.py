#!/usr/bin/env python3
"""Direct bundled-checker tests; full sandboxed Comparator is a separate check."""
from pathlib import Path
import hashlib,json,subprocess
root=Path(__file__).resolve().parents[1]
wrapper=['bash',str(root/'scripts/with-lean.sh')]
binary=Path(subprocess.check_output(wrapper+['lean','--print-prefix'],text=True).strip())/'bin'
out=root/'build';out.mkdir(exist_ok=True)
export=out/'solution.export.jsonl'
with export.open('w') as f:
 subprocess.run(wrapper+['lake','env','leanexport','Solution','--','DensityThreeQuarters.density_bound'],stdout=f,check=True)
config=out/'nanoda.json'
config.write_text(json.dumps({'use_stdin':False,'export_file_path':str(export),'permitted_axioms':['propext','Classical.choice','Quot.sound'],'unpermitted_axiom_hard_error':True,'num_threads':4,'nat_extension':True,'string_extension':True}))
checks=[]
for name,args in [('leanchecker',['--from-export',str(export)]),('nanoda_bin',[str(config)]),('con-ron',[str(export)])]:
 with (out/(name+'.log')).open('w') as f:
  subprocess.run([str(binary/name),*args],stdout=f,stderr=subprocess.STDOUT,check=True)
 checks.append({'checker':name,'exit_code':0,'binary_sha256':hashlib.sha256((binary/name).read_bytes()).hexdigest()})
(out/'direct-kernel-results.json').write_text(json.dumps({'scope':'Direct checks, not a sandboxed Comparator receipt','export_sha256':hashlib.sha256(export.read_bytes()).hexdigest(),'checks':checks},indent=2)+'\n')
print('PASS: direct Lean, NanoDa and con-ron export checks.')
