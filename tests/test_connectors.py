import unittest
from smt_encoding.constraints.connector_factory import add_eq, add_lt, add_not, add_leq, add_and, add_implies, add_or
from smt_encoding.constraints.connector import Connector

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

    def test_connector_and_with_false(self):
        formula = add_and(add_and("x", "u"), add_and("v", "w"), True, False)
        expected_result = False
        self.assertEqual(formula, expected_result)

    def test_connector_and_with_true(self):
        formula = add_and(True, add_and("x", "u"), True, add_and("v", "w"), True)
        expected_result = Connector("and", True, "w", "x", "u", "v")
        self.assertEqual(formula, expected_result)

    def test_and_one_term(self):
        formula = add_and(True, add_lt("v", "w"), True)
        expected_result = Connector("lt", False, "v", "w")
        self.assertEqual(formula, expected_result)

    def test_connector_and_nested(self):
        formula = add_and(True, add_and("u", False), add_and("x"))
        expected_result = False
        self.assertEqual(formula, expected_result)

    def test_connector_and_flattened(self):
        formula = add_and(True, add_and(add_and("x", "x"), add_and("u")), True, add_and("v", "w"), True)
        expected_result = Connector("and", True, "u", "w", "x", "x", "v")
        self.assertEqual(formula, expected_result)

    def test_connector_or_with_false(self):
        formula = add_or(False, add_and("x", "x"), "u", False)
        expected_result = Connector("or", True, "u", Connector("and", True, "x", "x"))
        self.assertEqual(formula, expected_result)

    def test_connector_or_with_true(self):
        formula = add_or(True, add_and("x", "u"), True, add_and("v", "w"), True)
        expected_result = True
        self.assertEqual(formula, expected_result)

    def test_or_one_term(self):
        formula = add_or(False, add_lt("v", "w"), False)
        expected_result = Connector("lt", False, "v", "w")
        self.assertEqual(formula, expected_result)

    def test_connector_or_nested(self):
        formula = add_or(False, add_or("u", add_or("y", "z", "x")), add_or("x"))
        expected_result = Connector("or", True, "u", "y", "z", "x", "x")
        self.assertEqual(formula, expected_result)

    def test_connector_or_flattened(self):
        formula = add_or(False, add_or(add_or("x", "x"), add_or("u", "a")), False, add_or("v", "w"), False)
        expected_result = Connector("or", True, "u", "w", "x", "x", "v", "a")
        self.assertEqual(formula, expected_result)

    def test_odd_nested_not(self):
        formula = add_not(add_not(add_not(add_not(add_not("a")))))
        expected_result = add_not("a")
        self.assertEqual(formula, expected_result)

    def test_even_nested_not(self):
        formula = add_not(add_not(add_not(add_not(add_not(add_not("a"))))))
        expected_result = "a"
        self.assertEqual(formula, expected_result)

    def test_bool_not(self):
        formula = add_not(True)
        expected_result = False
        self.assertEqual(formula, expected_result)

    def test_connector_implies_false_lhs(self):
        formula = add_implies(False, add_and("u", "v", "w"))
        expected_result = True
        self.assertEqual(formula, expected_result)

    def test_connector_implies_false_rhs(self):
        formula = add_implies(add_and("u", "v", "w"), False)
        expected_result = add_not(add_and("u", "v", "w"))
        self.assertEqual(formula, expected_result)

    def test_connector_implies_true_lhs(self):
        formula = add_implies(True, add_and("u", "v", "w"))
        expected_result = add_and("u", "v", "w")
        self.assertEqual(formula, expected_result)

    def test_connector_implies_true_rhs(self):
        formula = add_implies(add_and("u", "v", "w"), True)
        expected_result = True
        self.assertEqual(formula, expected_result)

    def test_eq_true_false(self):
        formula = add_eq(True, False)
        expected_results = False
        self.assertEqual(formula, expected_results)

    def test_eq_same_var(self):
        formula = add_eq(add_and(True, "a", "b"), add_and("b", "a"))
        expected_result = True
        self.assertEqual(formula, expected_result)

    def test_eq_diff_var(self):
        formula = add_eq(add_and(True, "d", "b"), add_and("b", "a"))
        expected_result = add_eq(add_and(True, "d", "b"), add_and("b", "a"))
        self.assertEqual(formula, expected_result)

    def test_eq_bool_int(self):
        formula = add_eq(True, 3)
        expected_result = False
        self.assertEqual(formula, expected_result)

    def test_nested_operations(self):
        formula = add_and(add_not(add_implies(add_eq("a", "b"), add_not(add_eq(add_or("u", False), add_and("u", True))))),
                          add_implies(add_eq(2, 3), "a"), True)
        expected_result = add_eq("b", "a")
        self.assertEqual(formula, expected_result)


if __name__ == '__main__':
    unittest.main()
