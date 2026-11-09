"""Bundle boundary tests: no original file access or implicit evidence credit."""
import copy
import hashlib
import tempfile
import unittest
from pathlib import Path
from stage1.contracts import check_evidence
from stage2.bundle_reader import BundleReader

class BundleReaderTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.base=Path(self.tmp.name)
        self.root=self.base/'input';self.root.mkdir()
        self.bundle=self.base/'bundle';self.bundle.mkdir()
        self.text='int f(void) {\n    return 1;\n}\n'
        (self.bundle/'source.c').write_text(self.text)
        sha=hashlib.sha256(self.text.encode()).hexdigest()
        self.manifest={'files':{'source.c':sha},'mappings':[{'original':{'path':'lib/f.c','start':10,'end':12},'bundle':{'path':'source.c','start':1,'end':3},'sha256':'original-source-hash'}]}
    def reader(self,manifest=None):
        return BundleReader(self.root,self.base/'reads.jsonl',bundles=[(self.bundle,manifest or self.manifest)])
    def test_original_coordinates_without_original_file(self):
        r=self.reader()
        self.assertFalse((self.root/'lib/f.c').exists())
        result=r.execute({'tool':'read','path':'lib/f.c','start':10,'count':3})
        self.assertEqual([x['line'] for x in result['lines']],[10,11,12])
        self.assertEqual(check_evidence([{'path':'lib/f.c','start':10,'end':12}],r),[])
    def test_missing_lines_never_get_evidence_credit(self):
        r=self.reader()
        self.assertIn('error',r.execute({'tool':'read','path':'lib/f.c','start':9,'count':4}))
        self.assertTrue(check_evidence([{'path':'lib/f.c','start':9,'end':12}],r))
        self.assertIn('error',r.execute({'tool':'read','path':'lib/not-extracted.c','start':1,'count':1}))
    def test_independent_reader_requires_own_reads(self):
        r=self.reader();r.execute({'tool':'read','path':'lib/f.c','start':10,'count':3})
        self.assertTrue(check_evidence([{'path':'lib/f.c','start':10,'end':12}],self.reader()))
    def test_tampering_rejected_on_read(self):
        r=self.reader();(self.bundle/'source.c').write_text('changed')
        self.assertIn('error',r.execute({'tool':'read','path':'lib/f.c','start':10,'count':3}))
    def test_mapping_cannot_escape_verified_files(self):
        outside=self.base/'outside.c';outside.write_text(self.text)
        for path in ('../outside.c',str(outside),'unlisted.c'):
            with self.subTest(path=path):
                (self.bundle/'unlisted.c').write_text(self.text)
                m=copy.deepcopy(self.manifest);m['mappings'][0]['bundle']['path']=path
                with self.assertRaises(ValueError):self.reader(m)
    def test_mapping_requires_integer_positive_copy_range(self):
        for start,end in ((0,3),(True,3),(1,False),(1,2),(4,3)):
            with self.subTest(start=start,end=end):
                m=copy.deepcopy(self.manifest);m['mappings'][0]['bundle'].update(start=start,end=end)
                with self.assertRaises(ValueError):self.reader(m)
    def test_conflicting_overlapping_snippets_rejected(self):
        m=copy.deepcopy(self.manifest)
        (self.bundle/'other.c').write_text('different\n')
        m['files']['other.c']=hashlib.sha256(b'different\n').hexdigest()
        mapping=copy.deepcopy(m['mappings'][0]);mapping['original'].update(start=11,end=11);mapping['bundle'].update(path='other.c',start=1,end=1)
        m['mappings'].append(mapping)
        with self.assertRaises(ValueError):self.reader(m)
    def test_mixed_source_versions_rejected(self):
        m=copy.deepcopy(self.manifest);other=copy.deepcopy(m['mappings'][0]);other['sha256']='different-hash';m['mappings'].append(other)
        with self.assertRaises(ValueError):self.reader(m)
    def test_search_is_explicitly_bundle_scoped(self):
        r=self.reader();result=r.execute({'tool':'search','path':'.','query':'return'})
        self.assertEqual(len(result['matches']),1)
        self.assertIn('absence is not absence',result['coverage'])
    def test_search_output_caps_long_source_lines(self):
        text='a'*30000+'\n';(self.bundle/'source.c').write_text(text)
        m=copy.deepcopy(self.manifest);m['files']['source.c']=hashlib.sha256(text.encode()).hexdigest()
        m['mappings'][0]['original'].update(start=10,end=10);m['mappings'][0]['bundle'].update(start=1,end=1)
        result=self.reader(m).execute({'tool':'search','path':'.','query':'a'})
        self.assertLessEqual(len(result['matches'][0]['text']),300)

if __name__=='__main__':unittest.main()
