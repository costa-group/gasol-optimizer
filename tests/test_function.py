import unittest
from smt_encoding.constraints.function import Function, Sort, ExpressionReference


class TestFunctionEncoding(unittest.TestCase):
    def test_declare_no_sort_function(self):
        self.assertRaises(ValueError, Function, 'a')

    def test_declare_const(self):
        a = Function('a', Sort.integer)
        self.assertEqual(a.name, 'a', "Function name does not match")
        self.assertEqual(a.arity, 0, "Function arity does not match")
        self.assertEqual(a.type, (Sort.integer,), "Function types do not match")

    def test_declare_function(self):
        f = Function('f', Sort.integer, Sort.boolean, Sort.boolean)
        self.assertEqual(f.name, 'f', "Function name does not match")
        self.assertEqual(f.arity, 2, "Function arity does not match")
        self.assertEqual(f.type, (Sort.integer, Sort.boolean, Sort.boolean), "Function types do not match")

    def test_constant_creation(self):
        a_as_function = Function('a', Sort.integer)
        a_as_constant = a_as_function()
        self.assertEqual(type(a_as_function), Function)
        self.assertEqual(type(a_as_constant), ExpressionReference)
        self.assertEqual(a_as_constant.type, Sort.integer)
        self.assertEqual(a_as_function.range, Sort.integer)

    def test_nested_function_expression(self):
        f = Function('f', Sort.integer, Sort.integer)
        a = Function('a', Sort.integer)()
        new_expression = f(f(f(a)))
        self.assertEqual(new_expression.type, Sort.integer)
        self.assertEqual(new_expression.arguments[0], f(f(a)))
        self.assertEqual(new_expression, f(f(f(a))))
        self.assertNotEqual(new_expression.arguments[0], f(f(f(a))))

    def test_argument_mismatch_function(self):
        f = Function('f', Sort.integer, Sort.integer)
        a = Function('a', Sort.boolean)()
        self.assertRaises(ValueError, f, a)

if __name__ == '__main__':
    unittest.main()
