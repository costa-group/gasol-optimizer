import unittest
from smt_encoding.constraints.connector_factory import add_eq, add_lt, add_not, add_leq, add_and, add_implies, add_or


class TestConnectors(unittest.TestCase):

    def test_commutative_correct(self):

        formula1 = add_implies(add_eq("t_1", 0), add_and(add_leq(0, "a_1"), add_lt("a_1", 2 ** 256),
                                                         add_not("u_1_1"), "u_0_2", add_eq("x_0_2", "a_1")))
        formula2 = add_implies(add_eq(0, "t_1"), add_and(add_leq(0, "a_1"), add_not("u_1_1"),
                                                         add_lt("a_1", 2 ** 256),
                                                         add_eq("a_1", "x_0_2"), "u_0_2",))
        self.assertEqual(formula1, formula2)

    def test_commutative_incorrect(self):
        formula1 = add_implies(add_eq("t_1", 0), add_and(add_leq(0, "a_1"), add_lt(2 ** 256, "a_1"),
                                                         add_not("u_1_1"), "u_0_2", add_eq("x_0_2", "a_1")))
        formula2 = add_implies(add_eq(0, "t_1"), add_and(add_leq(0, "a_1"), add_not("u_1_1"),
                                                         add_lt("a_1", 2 ** 256),
                                                         add_eq("a_1", "x_0_2"), "u_0_2",))
        self.assertNotEqual(formula1, formula2)

    def test_commutative_triple_nested(self):
        formula1 = add_implies(add_eq("t_1", 0), add_and(add_leq(0, "a_1"), add_lt("a_1", 2 ** 256),
                                                         add_not("u_1_1"), "u_0_2", add_eq(add_or("a_2", 5, True), "a_1")))
        formula2 = add_implies(add_eq(0, "t_1"), add_and(add_not("u_1_1"),
                                                         add_leq(0, "a_1"),
                                                         add_lt("a_1", 2 ** 256),
                                                         add_eq("a_1", add_or(5, True, "a_2")), "u_0_2",))
        self.assertEqual(formula1, formula2)


if __name__ == '__main__':
    unittest.main()
