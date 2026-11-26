import { evaluateClaims } from '../../../../src/core/claims.js';
const ents = [];
const E = (id, kind, data, owner=null) => { const e = {id, kind, data:{id, ...data}, owner, path:[], loc:{line:1,col:1,offset:0,length:1}}; ents.push(e); return e; };
// Components: X (component), S (subsystem) containing s1, Y (component)
E('X','component',{name:'X',category:'svc'});
E('S','component',{name:'S',category:'svc',kind:'subsystem'});
E('s1','component',{name:'s1',category:'svc',parent:'S'});
E('Y','component',{name:'Y',category:'svc'});
E('r1','relationship',{kind:'calls',from:'X',to:'S'});
E('r2','relationship',{kind:'calls',from:'s1',to:'Y'});
// Two contradictory assumptions
E('a-yes','assumption',{statement:'X calls Y on every request.'});
E('a-no','assumption',{statement:'X never calls Y, directly or indirectly.'});
// Claim 1: X never reaches Y (transitively) -- composition X->S, S contains s1, s1->Y
E('c1','claim',{kind:'structural',statement:'X never depends on Y, even indirectly.',assumptions:['a-no'],evaluate:{method:'no-relationship',from:'X',to:'Y',transitive:true}});
// Claim 2: same check, contradictory assumption
E('c2','claim',{kind:'structural',statement:'Calls are acyclic.',assumptions:['a-yes'],evaluate:{method:'acyclic'}});
// Claim 3: c1 again, with no assumptions at all
E('c3','claim',{kind:'structural',statement:'X never depends on Y (no assumptions).',assumptions:[],evaluate:{method:'no-relationship',from:'X',to:'Y',transitive:true}});
// Claim 4: S (with its children) is reached by X and S reaches Y -- both directions hold
E('c4','claim',{kind:'structural',statement:'X reaches S.',evaluate:{method:'reachable',from:'X',to:'S'}});
E('c5','claim',{kind:'structural',statement:'S reaches Y.',evaluate:{method:'reachable',from:'S',to:'Y'}});
const byKind = {}; for (const e of ents) (byKind[e.kind] ??= []).push(e);
const model = { entities: new Map(ents.map(e=>[e.id,e])), byKind, refs:[], exprs:[], semanticHash:'demo',
  meta:{ relationshipKinds:{calls:{label:'calls',dependency:true}}, categories:{svc:{label:'svc'}}, verificationMethods:{}, entities:{}, sections:{} } };
for (const r of evaluateClaims(model)) console.log(r.claimId, r.status, '| assumptions:', JSON.stringify(r.assumptions), '|', r.explanation.slice(0,160));
