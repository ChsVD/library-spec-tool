"""Atomic, replay-safe report batches. Validation remains a separate final gate."""
import copy
import hashlib
import json


def merge(previous, action, batches):
    fields=action.get('fields',{})
    additions=action.get('append',{})
    if not isinstance(fields,dict) or not isinstance(additions,dict) or not (fields or additions):
        raise ValueError('report_part needs nonempty fields or append objects')
    if set(fields)&set(additions):raise ValueError('cannot replace and append the same field in one batch')
    if any(not isinstance(v,list) or not v for v in additions.values()):
        raise ValueError('append values must be nonempty lists')
    ident=action.get('batch_id')
    if additions and (not isinstance(ident,str) or not ident.strip() or len(ident)>80):
        raise ValueError('append requires a stable batch_id of 1-80 characters')
    fingerprint=hashlib.sha256(json.dumps({'fields':fields,'append':additions},sort_keys=True,ensure_ascii=False).encode()).hexdigest()
    if ident is not None:
        if not isinstance(ident,str) or not ident.strip() or len(ident)>80:raise ValueError('invalid batch_id')
        if ident in batches:
            if batches[ident]!=fingerprint:raise ValueError('batch_id already used with different content; use a new ID')
            return copy.deepcopy(previous or {}),True
    combined=copy.deepcopy(previous or {})
    combined.update(copy.deepcopy(fields))
    for key,items in additions.items():
        if key in combined and not isinstance(combined[key],list):raise ValueError('cannot append to non-list field: '+key)
        combined.setdefault(key,[]).extend(copy.deepcopy(items))
    # Caller commits the batch ledger only after all size/time checks.
    return combined,False


def fingerprint(action):
    return hashlib.sha256(json.dumps({'fields':action.get('fields',{}),'append':action.get('append',{})},sort_keys=True,ensure_ascii=False).encode()).hexdigest()
