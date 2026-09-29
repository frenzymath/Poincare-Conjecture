import fs from 'node:fs';
import crypto from 'node:crypto';
import {execFileSync} from 'node:child_process';

const sourceRoot = process.argv[2];
if (!sourceRoot) throw new Error('Pass the pinned public checkout');
const pin = execFileSync('git',['rev-parse','HEAD'],{cwd:sourceRoot,encoding:'utf8'}).trim();
if(pin!=='60de1a94ca7038d04ed123b490a3229f8aa5fa75')throw new Error('Unexpected source pin');
const dir='references/ricci-flow/mapher/complete-import';
const rows=JSON.parse(fs.readFileSync(`${dir}/reconciliation.json`)).entries
  .filter(r=>r.source.startsWith('PoincareMT/Proofs/M76')&&r.source.endsWith('.lean'));
const pinnedFiles = execFileSync('git',['ls-tree','-r','--name-only','HEAD','PoincareMT/Proofs/M76','PoincareMT/Proofs/M76.lean'],{cwd:sourceRoot,encoding:'utf8'}).trim().split('\n').filter(f=>f.endsWith('.lean'));
const scannedSources = new Set(rows.map(r=>r.source));
const missingSourceMappings = pinnedFiles.filter(f=>!scannedSources.has(f));
if(missingSourceMappings.length)throw new Error(`Missing M76 source mappings: ${missingSourceMappings.join(', ')}`);
const hash=s=>crypto.createHash('sha256').update(s).digest('hex');
function maskComments(t){
  let out='',depth=0,quoted=false;
  for(let i=0;i<t.length;){let pair=t.slice(i,i+2);
    if(depth){if(pair==='/-'){depth++;out+='  ';i+=2;}else if(pair==='-/'){depth--;out+='  ';i+=2;}else{out+=t[i]==='\n'?'\n':' ';i++;}}
    else if(quoted){out+=t[i];if(t[i]==='\\'){out+=t[i+1]??'';i+=2;}else{if(t[i]==='"')quoted=false;i++;}}
    else if(pair==='/-'){depth++;out+='  ';i+=2;}
    else if(pair==='--'){while(i<t.length&&t[i]!=='\n'){out+=' ';i++;}}
    else{if(t[i]==='"')quoted=true;out+=t[i++];}
  }return out;
}
function decls(raw){const t=maskComments(raw);return [...t.matchAll(/^([ \t]*(?:(?:private|protected|noncomputable|unsafe|public)\s+)*)(theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+([^\s:{([]+)/gm)]
  .map((m,i,a)=>({name:m[3],kind:m[2],private:/\bprivate\b/.test(m[1]),at:m.index,
    end:a[i+1]?.index??t.length,line:raw.slice(0,m.index).split('\n').length,
    text:raw.slice(m.index,a[i+1]?.index??t.length)}));}
const normalize=t=>maskComments(t).replace(/^\s*(?:public\s+)?import[^\n]*$/gm,'').replace(/\s+/g,' ').trim();
let targets=0,privates=0;const mismatches=[],unmapped=[];
for(const row of rows){
  if(!row.targets.length){unmapped.push({source:row.source,reason:row.reason??row.reconciliation});continue;}
  for(const target of row.targets){if(!fs.existsSync(target.target))continue;targets++;
    const dst=fs.readFileSync(target.target,'utf8'),dd=decls(dst),pd=dd.filter(d=>d.private);privates+=pd.length;
    if(!pd.length)continue;
    const src=fs.readFileSync(`${sourceRoot}/${row.source}`,'utf8'),sd=decls(src);
    for(const d of pd){const candidates=sd.filter(s=>s.name===d.name&&s.kind===d.kind&&!s.private);
      if(!candidates.length)continue;
      const matching=candidates.find(s=>normalize(s.text)===normalize(d.text.replace(/\bprivate\s+/,'')))??candidates[0];
      mismatches.push({source:row.source,target:target.target,name:d.name,kind:d.kind,
        source_line:matching.line,target_line:d.line,source_sha256:hash(src),target_sha256:hash(dst),
        source_public_matches:candidates.length,
        declaration_suffix_equal_after_private_removal:normalize(matching.text)===normalize(d.text.replace(/\bprivate\s+/,'')),
        file_equal_after_this_private_removal:normalize(src)===normalize(dst.slice(0,d.at)+dst.slice(d.at).replace(/\bprivate\s+/,'')),
        source_header:matching.text.slice(0,matching.text.indexOf(':=')).trim(),
        target_header:d.text.slice(0,d.text.indexOf(':=')).trim()});
    }
  }
}
const result={status:'Read-only deterministic visibility comparison; not a mathematical proof audit',
  primary_source_commit:pin,pinned_source_modules:pinnedFiles.length,missing_source_mappings:missingSourceMappings,mapped_source_modules:rows.length,checked_target_mappings:targets,
  workspace_private_declarations:privates,unmapped_sources:unmapped,mismatches};
fs.writeFileSync(new URL('./m76-visibility-scan.json',import.meta.url),JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify({...result,mismatches:mismatches.map(({source,target,name,declaration_suffix_equal_after_private_removal})=>({source,target,name,declaration_suffix_equal_after_private_removal}))}));
