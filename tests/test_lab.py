import itertools
import unittest
from fractions import Fraction
from lab import optimize, explore, bans
from verify import valid, score, verify, brute_force


class Lab(unittest.TestCase):
    def test_forbidden_masks(self):
        for a,b in itertools.combinations(range(1,35), 2):
            expected = sum(1 << (c-1) for c in range(b+1,35) if (b+c)%a == 0)
            self.assertEqual(bans(a,b,34), expected)

    def test_exact_against_oracle(self):
        for n in range(1, 15):
            for low in range(1, min(5,n)+1):
                witness, value, _, complete = optimize(n, low, 100000)
                self.assertTrue(complete)
                self.assertTrue(valid(witness))
                self.assertEqual(value, score(witness))
                self.assertEqual(value, brute_force(n,low))

    def test_budget_returns_witness_only(self):
        witness, value, nodes, complete = optimize(150, 1, 1)
        self.assertEqual(nodes, 1)
        self.assertFalse(complete)
        self.assertTrue(valid(witness))
        self.assertEqual(score(witness), value)

    def test_exploration_repeatable(self):
        a = explore(200, 2, 25, 42)
        self.assertEqual(a, explore(200, 2, 25, 42))
        self.assertTrue(valid(a[0]))
        self.assertFalse(a[3])

    def test_independent_verifier(self):
        rec = dict(schema=1,conjecture="property-p-sharp",witness=[1,2],min_element=1,n=10,
                   score="3/2",exceeds_target=False)
        self.assertEqual(verify(rec), Fraction(3,2))
        for witness in ([0,1],[1,2,3],[2,1],[2,2],[1,11],[2],[]):
            with self.assertRaises(ValueError):
                verify(dict(rec,witness=witness))
