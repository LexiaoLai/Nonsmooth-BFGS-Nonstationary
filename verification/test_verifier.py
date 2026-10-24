#!/usr/bin/env python3
"""Small regression tests for certificate failure modes and exact arithmetic."""
from fractions import Fraction as F
from pathlib import Path
import subprocess,sys,unittest
import verify
from intervals import IV
from polynomial import Algebraic,B

class CertificateTests(unittest.TestCase):
    def test_interval_containment(self):
        a=IV(F(-7,11),F(2,3));b=IV(F(1,7),F(8,9))
        result=a*b+a/b
        for x in (F(-7,11),F(0),F(2,3)):
            for y in (F(1,7),F(1,2),F(8,9)):
                self.assertLessEqual(result.lo,x*y+x/y)
                self.assertGreaterEqual(result.hi,x*y+x/y)
    def test_reject_unsafe_inputs(self):
        with self.assertRaises(TypeError):IV(0.1)
        with self.assertRaises(ZeroDivisionError):IV(1)/IV(-1,1)
        with self.assertRaises(ValueError):IV(2,1)
    def test_algebraic_arithmetic(self):
        self.assertEqual(verify.poly(B),0)
        z=2*B-1
        self.assertEqual(z*z.inverse(),1)
        self.assertEqual((B+1)*(B-1),B*B-1)
        with self.assertRaises(ZeroDivisionError):Algebraic(0).inverse()
    def test_shifted_root_box_is_rejected(self):
        old=verify.ROOT_LO
        try:
            verify.ROOT_LO=F('0.918')
            with self.assertRaises(ArithmeticError):verify.root_certificate()
        finally:verify.ROOT_LO=old
    def test_changed_matrix_is_rejected(self):
        old=verify.S[0][0]
        try:
            verify.S[0][0]+=1
            with self.assertRaises(ArithmeticError):verify.stability_certificate(IV(verify.ROOT_LO,verify.ROOT_HI))
        finally:verify.S[0][0]=old
    def test_full_certificate(self):
        r=verify.verify()
        self.assertEqual(r['cycle']['r'],F(64,81))
        lo,hi=r['root']['narrow']
        self.assertLess(verify.poly(lo),0)
        self.assertGreater(verify.poly(hi),0)
        self.assertEqual(hi-lo,F(1,10**11))
        self.assertEqual(r['stability']['rows'],list(map(sum,r['stability']['magnitude'])))
        for sharp_row,rounded_row in zip(r['stability']['matrix'],r['stability']['magnitude']):
            for sharp,rounded in zip(sharp_row,rounded_row):
                self.assertLessEqual(sharp.mag(),rounded)
                self.assertLess(rounded-sharp.mag(),F(1,1000))
        self.assertLessEqual(r['stability']['norm'],F('0.78'))
        for gap in r['bridges']['gaps']:
            self.assertGreaterEqual(gap['L'].lo,0)
            self.assertLessEqual(gap['R'].hi,0)
            self.assertGreater(gap['remaining'].lo,0)
            self.assertEqual([item['n'] for item in gap['rejected']],list(range(gap['n'])))
            self.assertTrue(all(item['fails'] for item in gap['rejected']))
        self.assertGreaterEqual(len(r['checks']),100)
    def test_least_bridge_rejects_earlier_indices(self):
        left=dict(t=IV(0),eta=IV(0),d=IV(1),k=IV(0))
        right=dict(t=IV(1),eta=IV(1),d=IV(1),k=IV(3))
        bridge=verify.least_bridge(left,right,'test')
        self.assertEqual(bridge['n'],2)
        self.assertEqual([item['n'] for item in bridge['rejected']],[0,1])
        self.assertTrue(all('R>0' in item['fails'] for item in bridge['rejected']))
    def test_bridge_rejects_nonmonotone_data(self):
        left=dict(t=IV(0),eta=IV(0),d=IV(F(1,200)),k=IV(0))
        right=dict(t=IV(1),eta=IV(1),d=IV(1),k=IV(0))
        with self.assertRaises(ArithmeticError):verify.least_bridge(left,right,'invalid')
    def test_identity_bridge_rejects_exact_zero_margin(self):
        left=dict(t=IV(-2),eta=IV(-2),d=IV(1),k=IV(0))
        right=dict(t=IV(-1),eta=IV(-1),d=IV(1),k=IV(0))
        bridge=verify.least_bridge(left,right,'identity')
        self.assertEqual(bridge['n'],1)
        self.assertEqual(bridge['rejected'],[dict(n=0,fails=['Delta-I<=0'])])
    def test_optimized_python_is_rejected(self):
        r=subprocess.run([sys.executable,'-O',str(Path(verify.__file__))],capture_output=True,text=True)
        self.assertNotEqual(r.returncode,0)
        self.assertIn('without Python',r.stderr)

if __name__=='__main__':unittest.main()
